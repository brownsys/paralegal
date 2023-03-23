use std::{borrow::Cow, cell::RefCell, fmt::Display, ops::Index, rc::Rc};

use crate::{
    ir::global_location::{GliAt, GlobalLocation, IsGlobalLocation, GLI},
    mir,
    rust::{
        mir::{visit::Visitor, *},
        rustc_data_structures::fx::{FxHashMap as HashMap, FxHashSet as HashSet},
        rustc_hir::{def_id::DefId, BodyId},
        rustc_mir_dataflow::{self, Analysis, AnalysisDomain, Forward, JoinSemiLattice},
        ty::{subst::GenericArgKind, ClosureKind, TyCtxt, TyKind},
    },
    ty,
    utils::SparseMatrix,
    Symbol,
};

use flowistry::{
    extensions::{is_extension_active, ContextMode, MutabilityMode, RecurseSelector},
    indexed::{impls::LocationDomain, IndexMatrix, IndexSet, IndexedDomain, RefSet},
    infoflow::mutation::{ModularMutationVisitor, MutationStatus},
    mir::{
        aliases::Aliases,
        borrowck_facts::{get_body_with_borrowck_facts, CachedSimplifedBodyWithFacts},
        control_dependencies::ControlDependencies,
        engine,
        engine::AnalysisResults,
        utils::{BodyExt, OperandExt, PlaceExt},
    },
};

pub type FlowResults<'a, 'tcx, 'g> = engine::AnalysisResults<'tcx, FlowAnalysis<'a, 'tcx, 'g>>;

pub type Dependency<'tcx> = (Location, Place<'tcx>);
pub type LocationSet<'tcx> = HashSet<Dependency<'tcx>>;
pub type DependencyMap<'tcx> = SparseMatrix<Place<'tcx>, Dependency<'tcx>>;

#[derive(PartialEq, Eq, Clone, Default, Debug)]
pub struct FlowDomain<'tcx> {
    matrix: DependencyMap<'tcx>,
    overrides: DependencyMap<'tcx>,
}

impl<'tcx> DependencyMap<'tcx> {
    pub fn fmt_indent(&self, f: &mut std::fmt::Formatter<'_>, indent: usize) -> std::fmt::Result {
        for (k, v) in self.rows() {
            write!(f, "{:indent$}{k:?}: {{", ' ')?;
            let mut first = true;
            for (loc, place) in v {
                if first {
                    first = false;
                } else {
                    f.write_str(", ")?;
                }
                write!(f, "{place:?}@{loc:?}")?;
            }
            writeln!(f, "}}")?;
        }
        Ok(())
    }
}

impl<'tcx> Display for FlowDomain<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "before:")?;
        self.matrix.fmt_indent(f, 2)?;
        writeln!(f, "after:")?;
        self.overrides.fmt_indent(f, 2)
    }
}

impl<'tcx> FlowDomain<'tcx> {
    pub fn deps(&self, at: Place<'tcx>) -> impl Iterator<Item = &Dependency<'tcx>> {
        self.matrix()[&at].iter()
    }
    fn override_(&mut self, row: Place<'tcx>, at: Dependency<'tcx>) -> bool {
        self.overrides.set(row, at)
    }
    fn matrix(&self) -> &DependencyMap<'tcx> {
        &self.matrix
    }
    fn matrix_mut<'a>(&mut self) -> &mut DependencyMap<'tcx> {
        &mut self.matrix
    }
    fn union_after(&mut self, row: Place<'tcx>, from: Cow<LocationSet<'tcx>>) -> bool {
        self.overrides.union_row(&row, from)
    }
    fn from_location_domain(dom: &Rc<LocationDomain>) -> Self {
        Self {
            ..Default::default()
        }
    }
    fn include(&mut self, row: Place<'tcx>, at: Dependency<'tcx>) -> bool {
        self.override_(row, at)
    }
    fn rows_after_override(&self) -> impl Iterator<Item = (&Place<'tcx>, &LocationSet<'tcx>)> {
        self.matrix
            .rows()
            .filter(|r| !self.overrides.has(&r.0))
            .chain(self.overrides.rows())
    }
}

impl<'tcx> JoinSemiLattice for FlowDomain<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (k, v) in other.rows_after_override() {
            changed |= self.matrix_mut().union_row(k, Cow::Borrowed(v));
        }
        changed
    }
}

pub struct FlowAnalysis<'a, 'tcx, 'g> {
    pub tcx: TyCtxt<'tcx>,
    pub def_id: DefId,
    pub body: &'a Body<'tcx>,
    pub control_dependencies: ControlDependencies,
    pub aliases: Aliases<'a, 'tcx>,
    pub gli: GLI<'g>,
    recurse_cache: RefCell<HashMap<BodyId, FlowResults<'a, 'tcx, 'g>>>,
    recurse_selector: &'a dyn RecurseSelector,
}

impl<'a, 'tcx, 'g> FlowAnalysis<'a, 'tcx, 'g> {
    fn body_id(&self) -> BodyId {
        self.tcx.hir().body_owned_by(
            self.tcx
                .hir()
                .local_def_id_to_hir_id(self.def_id.expect_local()),
        )
    }

    pub fn new(
        tcx: TyCtxt<'tcx>,
        gli: GLI<'g>,
        def_id: DefId,
        body: &'a Body<'tcx>,
        aliases: Aliases<'a, 'tcx>,
        control_dependencies: ControlDependencies,
        recurse_selector: &'a dyn RecurseSelector,
    ) -> Self {
        let recurse_cache = RefCell::new(HashMap::default());
        FlowAnalysis {
            tcx,
            gli,
            def_id,
            body,
            aliases,
            control_dependencies,
            recurse_cache,
            recurse_selector,
        }
    }

    pub fn location_domain(&self) -> &Rc<LocationDomain> {
        self.aliases.location_domain()
    }

    pub fn gli_at(&self, location: Location) -> GliAt<'g> {
        self.gli.at(location, self.body_id())
    }
    fn transfer_function(
        &self,
        state: &mut FlowDomain<'tcx>,
        mutated: Place<'tcx>,
        inputs: &[(Place<'tcx>, Option<PlaceElem<'tcx>>)],
        location: Location,
        mutation_status: MutationStatus,
        transitive: bool,
    ) {
        debug!("  Applying mutation to {mutated:?} with inputs {inputs:?}");
        let location_domain = self.location_domain();

        let all_aliases = &self.aliases;
        let mutated_aliases = all_aliases.aliases(mutated);
        trace!("    Mutated aliases: {mutated_aliases:?}");
        assert!(!mutated_aliases.is_empty());

        // Clear sub-places of mutated place (if sound to do so)
        // if matches!(mutation_status, MutationStatus::Definitely) && mutated_aliases.len() == 1 {
        //     let mutated_direct = mutated_aliases.iter().next().unwrap();
        //     for sub in all_aliases.children(*mutated_direct).iter() {
        //         state.matrix_mut().clear_row(all_aliases.normalize(*sub));
        //     }
        // }

        let mut input_location_deps = LocationSet::default();
        if !transitive {
            input_location_deps.insert((location, mutated));
        }

        let add_deps = |place: Place<'tcx>, location_deps: &mut LocationSet<'tcx>| {
            if !transitive {
                return;
            }
            //let reachable_values = all_aliases.reachable_values(place, Mutability::Not);
            let reachable_values = all_aliases.children(place);
            let provenance = place
                .refs_in_projection()
                .into_iter()
                .flat_map(|(place_ref, _)| {
                    all_aliases
                        .aliases(Place::from_ref(place_ref, self.tcx))
                        .iter()
                });
            for relevant in reachable_values.iter().chain(provenance) {
                let deps = state.matrix().row(&all_aliases.normalize(*relevant));
                trace!("    For relevant {relevant:?} for input {place:?} adding deps {deps:?}");
                location_deps.extend(deps.iter());
            }
        };

        // Add deps of mutated to include provenance of mutated pointers
        add_deps(mutated, &mut input_location_deps);

        // Add deps of all inputs
        let mut children = Vec::new();
        for (place, elem) in inputs.iter() {
            add_deps(*place, &mut input_location_deps);

            // If the input is associated to a specific projection of the mutated
            // place, then save that input's dependencies with the projection
            if let Some(elem) = elem {
                let mut projection = mutated.projection.to_vec();
                projection.push(*elem);
                let mut child_deps = LocationSet::default();
                add_deps(*place, &mut child_deps);
                children.push((
                    Place::make(mutated.local, &projection, self.tcx),
                    child_deps,
                ));
            }
        }

        if children.len() > 0 {
            // In the special case of mutated = aggregate { x: .., y: .. }
            // then we ensure that deps(mutated.x) != deps(mutated)

            // // First, ensure that all children have the current in their deps.
            // // See test struct_read_constant for where this is needed.
            // for child in all_aliases.children(mutated) {
            //     state.include(all_aliases.normalize(child), location);
            // }

            // Then for constructor arguments that were places, add dependencies of those places.
            for (child, deps) in children {
                state.union_after(all_aliases.normalize(child), Cow::Owned(deps));
            }

            // Finally add input_location_deps *JUST* to mutated, not conflicts of mutated.
            state.union_after(
                all_aliases.normalize(mutated),
                Cow::Owned(input_location_deps),
            );
        } else {
            // Union dependencies into all conflicting places of the mutated place
            let mut mutable_conflicts = Cow::Borrowed(all_aliases.conflicts(mutated));

            // Remove any conflicts that aren't actually mutable, e.g. if x : &T ends up
            // as an alias of y: &mut T. See test function_lifetime_alias_mut for an example.
            let ignore_mut =
                is_extension_active(|mode| mode.mutability_mode == MutabilityMode::IgnoreMut);
            if !ignore_mut {
                let body = self.body;
                let tcx = self.tcx;
                let cfl = mutable_conflicts
                    .iter()
                    .filter(|place| {
                        place.iter_projections().all(|(sub_place, _)| {
                            let ty = sub_place.ty(body.local_decls(), tcx).ty;
                            !matches!(ty.ref_mutability(), Some(Mutability::Not))
                        })
                    })
                    .copied()
                    .collect::<HashSet<_>>();
                mutable_conflicts = Cow::Owned(cfl)
            };

            debug!("  Mutated conflicting places: {mutable_conflicts:?}");
            debug!("    with deps {input_location_deps:?}");

            for place in mutable_conflicts.into_owned().into_iter() {
                state.union_after(
                    all_aliases.normalize(place),
                    Cow::Borrowed(&input_location_deps),
                );
            }
        }
    }
}

impl<'a, 'tcx, 'g> AnalysisDomain<'tcx> for FlowAnalysis<'a, 'tcx, 'g> {
    type Domain = FlowDomain<'tcx>;
    type Direction = Forward;
    const NAME: &'static str = "FlowAnalysis";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        FlowDomain::default()
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        for (arg, loc) in self.aliases.all_args() {
            for place in self.aliases.conflicts(arg) {
                debug!(
                    "arg={arg:?} / place={place:?} / loc={:?}",
                    self.location_domain().value(loc)
                );
                state.matrix_mut().set(
                    self.aliases.normalize(*place),
                    (*self.location_domain().value(loc), *place),
                );
            }
        }
    }
}

impl<'a, 'tcx, 'g> Analysis<'tcx> for FlowAnalysis<'a, 'tcx, 'g> {
    fn apply_statement_effect(
        &self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        ModularMutationVisitor::new(
            &self.aliases,
            |mutated: Place<'tcx>,
             inputs: &[(Place<'tcx>, Option<PlaceElem<'tcx>>)],
             location: Location,
             mutation_status: MutationStatus| {
                self.transfer_function(state, mutated, inputs, location, mutation_status, true)
            },
        )
        .visit_statement(statement, location);
    }

    fn apply_terminator_effect(
        &self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        ModularMutationVisitor::new(
            &self.aliases,
            |mutated: Place<'tcx>,
             inputs: &[(Place<'tcx>, Option<PlaceElem<'tcx>>)],
             location: Location,
             mutation_status: MutationStatus| {
                self.transfer_function(
                    state,
                    mutated,
                    inputs,
                    location,
                    mutation_status,
                    !matches!(&terminator.kind, TerminatorKind::Call { .. }),
                )
            },
        )
        .visit_terminator(terminator, location);
    }

    fn apply_call_return_effect(
        &self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: rustc_mir_dataflow::CallReturnPlaces<'_, 'tcx>,
    ) {
    }
}

pub fn compute_flow_internal<'a, 'tcx, 'g>(
    tcx: TyCtxt<'tcx>,
    gli: GLI<'g>,
    body_id: BodyId,
    body_with_facts: &'a CachedSimplifedBodyWithFacts<'tcx>,
    recurse_selector: &'a dyn RecurseSelector,
) -> FlowResults<'a, 'tcx, 'g> {
    flowistry::infoflow::BODY_STACK.with(|body_stack| {
    body_stack.borrow_mut().push(body_id);
    // debug!(
    //   "{}",
    //   rustc_hir_pretty::to_string(rustc_hir_pretty::NO_ANN, |s| s
    //     .print_expr(&tcx.hir().body(body_id).value))
    // );
    // debug!("{}", body_with_facts.simplified_body().to_string(tcx).unwrap());

    let def_id = tcx.hir().body_owner_def_id(body_id).to_def_id();
    let aliases = Aliases::build(tcx, def_id, body_with_facts);
    let location_domain = aliases.location_domain().clone();

    let body = body_with_facts.simplified_body();
    let control_dependencies = ControlDependencies::build(body);
    debug!("Control dependencies: {control_dependencies:?}");

    let results = {
      //block_timer!("Flow");

      let analysis = FlowAnalysis::new(tcx, gli, def_id, body, aliases, control_dependencies, recurse_selector);
      engine::iterate_to_fixpoint(tcx, body, location_domain, analysis)
      // analysis.into_engine(tcx, body).iterate_to_fixpoint()
    };

    if log::log_enabled!(log::Level::Info) {
      let counts = body
        .all_locations()
        .flat_map(|loc| {
          let state = results.state_at(loc).matrix();
          state
            .rows()
            .map(|(_, locations)| locations.len())
            .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

      let nloc = body.all_locations().count();
      let np = counts.len();
      let pavg = np as f64 / (nloc as f64);
      let nl = counts.into_iter().sum::<usize>();
      let lavg = nl as f64 / (nloc as f64);
      log::info!(
        "Over {nloc} locations, total number of place entries: {np} (avg {pavg:.0}/loc), total size of location sets: {nl} (avg {lavg:.0}/loc)",
      );
    }

    if std::env::var("DUMP_MIR").is_ok()
      && flowistry::infoflow::BODY_STACK.with(|body_stack| body_stack.borrow().len() == 1)
    {
      todo!()
      // utils::dump_results(body, &results, def_id, tcx).unwrap();
    }

    body_stack.borrow_mut().pop();

    results
  })
}
