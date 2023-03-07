use std::{cell::RefCell, rc::Rc};

use crate::{
    ir::global_location::{GlobalLocation, GLI, GliAt, IsGlobalLocation},
    rust::{
        mir::{visit::Visitor, *},
        rustc_data_structures::fx::{FxHashMap as HashMap, FxHashSet as HashSet},
        rustc_hir::{def_id::DefId, BodyId},
        rustc_mir_dataflow::{self, Analysis, AnalysisDomain, Forward, JoinSemiLattice},
        ty::{subst::GenericArgKind, ClosureKind, TyCtxt, TyKind},
    },
    Symbol,
    ty
};

use flowistry::{
    extensions::RecurseSelector,
    infoflow::mutation::{ModularMutationVisitor, MutationStatus},
    mir::{
        borrowck_facts::{get_body_with_borrowck_facts, CachedSimplifedBodyWithFacts},
        utils::{self, BodyExt}, engine::AnalysisResults,
    },
};
use flowistry::{
    extensions::{is_extension_active, ContextMode, MutabilityMode},
    indexed::{
        impls::{LocationDomain, LocationSet},
        IndexMatrix, IndexSet, IndexedDomain, RefSet,
    },
    mir::{
        aliases::Aliases,
        control_dependencies::ControlDependencies,
        engine,
        utils::{OperandExt, PlaceExt},
    },
};
use rustc_index::vec::IndexVec;

#[derive(PartialEq, Eq, Hash, Clone, Debug, Copy)]
pub struct GlobalPlace<'tcx, 'g> {
    place: Place<'tcx>,
    location: Option<GlobalLocation<'g>>,
}

impl<'tcx, 'g> GlobalPlace<'tcx, 'g> {
    fn from_local(place: Place<'tcx>) -> Self {
        GlobalPlace {
            place,
            location: None,
        }
    }

    fn is_return_place(self) -> bool {
        self.place.local == RETURN_PLACE
    }

    fn expect_local(self) -> Place<'tcx> {
        assert_eq!(self.location, None);
        self.place
    }

    fn is_local(self) -> bool {
        self.location.is_none()
    }
}

impl <'g> GliAt<'g> {
    pub fn relativize_place<'tcx>(&self, place: GlobalPlace<'tcx, 'g>) -> GlobalPlace<'tcx, 'g> {
        GlobalPlace { place: place.place, location: Some(place.location.map_or_else(|| self.as_global_location(), |prior| self.relativize(prior))) }
    }
}

use crate::ir::regal;

pub type FlowResults<'a, 'tcx, 'g> = engine::AnalysisResults<'tcx, FlowAnalysis<'a, 'tcx, 'g>>;

#[derive(Default, PartialEq, Eq, Hash, Clone)]
pub struct Dependency {
    wildcard: Option<Location>,
    on_path: HashMap<Path, Location>,
}

pub type DependencyMap = HashMap<Local, Dependency>;

pub type Path = regal::ProjectionDelta;



impl From<Location> for Dependency {
    fn from(location: Location) -> Self {
        Self { wildcard: Some(location), on_path: HashMap::default() }
    }
}

impl From<&'_ Location> for Dependency {
    fn from(location: &Location) -> Self {
        (*location).into()
    }
}

impl <'tcx> From<&ty::List<PlaceElem<'tcx>>> for Path {
    fn from(_: &ty::List<PlaceElem>) -> Self {
        unimplemented!()
    }
}

#[derive(PartialEq, Eq, Clone, Default)]
pub struct FlowDomain {
    matrix: DependencyMap,
    overrides: HashMap<Local, Dependency>,
}

fn projection_to_delta<'tcx>(l: &ty::List<PlaceElem<'tcx>>) -> Option<Path> {
    (!l.is_empty()).then(|| l.into())
}

impl FlowDomain {
    fn override_(&mut self, row: Place, at: Location) -> bool {
        let target = self.overrides.entry(row.local).or_default();
        let old = if let Some(as_delta) = projection_to_delta(row.projection) {
            target.on_path.insert(as_delta, at)
        } else {
            target.wildcard.replace(at)
        };
        if let Some(old) = old {
            if old != at {
                warn!("Duplicate override for key {row:?}, old:{old:?} new:{at:?}");
            }
        };
        old.is_none()
    }

    fn insert(&mut self, k: Place, v: Location) -> bool {
        let target = self.matrix.entry(k.local).or_default();
        if let Some(as_delta) = projection_to_delta(k.projection) {
            target.on_path.insert(as_delta, v)
        } else {
            target.wildcard.replace(v)
        }.is_none()
    }

    fn matrix(&self) -> &DependencyMap {
        &self.matrix
    }
    fn matrix_mut<'a>(&mut self) -> &mut DependencyMap {
        &mut self.matrix
    }
    fn row<'a>(&'a self, row: Place) -> &HashSet<Dependency> {
        //&self.matrix[&row]
        unimplemented!()
    }
    fn union_after(
        &mut self,
        row: Place,
        _from: &HashSet<Dependency>,
        at: Location,
    ) -> bool {
        self.override_(row, at)
    }
    fn include(&mut self, row: Place, at: Location) -> bool {
        self.override_(row, at)
    }
}

impl<'tcx> JoinSemiLattice for FlowDomain {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        other.matrix.iter().for_each(|(&r, s)| {
            if other.overrides.contains_key(&r) {
                changed |= false;
            } else {
                for i in s.iter() {
                    changed |= self.insert(r, *i)
                }
            };
        });
        other
            .overrides
            .iter()
            .for_each(|(&p, &l)| changed |= self.insert(p, l));
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
        state: &mut FlowDomain,
        mutated: Place<'tcx>,
        inputs: &[(Place<'tcx>, Option<PlaceElem<'tcx>>)],
        location: Location,
        mutation_status: MutationStatus,
        subfn_ana: Option<(BodyId, &AnalysisResults<'tcx, FlowAnalysis<'_, 'tcx, 'g>>)>
    ) {
        debug!("  Applying mutation to {mutated:?} with inputs {inputs:?}");

        let all_aliases = &self.aliases;
        let mutated_aliases = all_aliases.aliases(mutated);
        trace!("    Mutated aliases: {mutated_aliases:?}");
        assert!(!mutated_aliases.is_empty());
        let body_id = self.body_id();
        let gli = self.gli_at(location);
        let global_loc = location;

        // Clear sub-places of mutated place (if sound to do so)
        if matches!(mutation_status, MutationStatus::Definitely) && mutated_aliases.len() == 1 {
            let mutated_direct = mutated_aliases.iter().next().unwrap();
            for sub in all_aliases.children(*mutated_direct).iter() {
                state
                    .matrix_mut()
                    .remove(&all_aliases.normalize(*sub));
            }
        }

        let mut input_location_deps = HashSet::default();
        input_location_deps.insert(global_loc.into());

        let add_deps = |global_place: Place<'tcx>, location_deps: &mut HashSet<Dependency>| {
            let place = global_place;
            let reachable_values = {
                let aliases = all_aliases;
                aliases.reachable_values(place, Mutability::Not)
            };
            let provenance = place
                .refs_in_projection()
                .into_iter()
                .flat_map(|(place_ref, _)| {
                    all_aliases
                        .aliases(Place::from_ref(place_ref, self.tcx))
                        .iter()
                });
            for relevant in reachable_values.iter().chain(provenance) {
                let deps = state.row(all_aliases.normalize(*relevant));
                trace!("    For relevant {relevant:?} for input {place:?} adding deps {deps:?}");
                location_deps.extend(deps.iter().cloned());
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
                let mut child_deps = HashSet::default();
                add_deps(*place, &mut child_deps);
                children.push((
                    Place::make(mutated.local, &projection, self.tcx),
                    child_deps,
                ));
            }
        }

        // Add control dependencies
        let controlled_by = self.control_dependencies.dependent_on(location.block);
        let body = self.body;
        for block in controlled_by.into_iter().flat_map(|set| set.iter()) {
            input_location_deps.insert(
                body.terminator_loc(block).into(),
            );

            // Include dependencies of the switch's operand
            let terminator = body.basic_blocks()[block].terminator();
            if let TerminatorKind::SwitchInt { discr, .. } = &terminator.kind {
                if let Some(discr_place) = discr.to_place() {
                    add_deps(discr_place, &mut input_location_deps);
                }
            }
        }

        if children.len() > 0 {
            // In the special case of mutated = aggregate { x: .., y: .. }
            // then we ensure that deps(mutated.x) != deps(mutated)

            // First, ensure that all children have the current in their deps.
            // See test struct_read_constant for where this is needed.
            for child in all_aliases.children(mutated) {
                state.include(
                    all_aliases.normalize(child),
                    global_loc.into(),
                );
            }

            // Then for constructor arguments that were places, add dependencies of those places.
            for (child, deps) in children {
                state.union_after(
                    all_aliases.normalize(child),
                    &deps,
                    global_loc.into(),
                );
            }

            // Finally add input_location_deps *JUST* to mutated, not conflicts of mutated.
            state.union_after(
                all_aliases.normalize(mutated),
                &input_location_deps,
                global_loc.into(),
            );
        } else {
            // Union dependencies into all conflicting places of the mutated place
            let mut mutable_conflicts = all_aliases.conflicts(mutated).to_owned();

            // Remove any conflicts that aren't actually mutable, e.g. if x : &T ends up
            // as an alias of y: &mut T. See test function_lifetime_alias_mut for an example.
            let ignore_mut =
                is_extension_active(|mode| mode.mutability_mode == MutabilityMode::IgnoreMut);
            if !ignore_mut {
                let body = self.body;
                let tcx = self.tcx;
                mutable_conflicts = mutable_conflicts
                    .iter()
                    .filter(|place| {
                        place.iter_projections().all(|(sub_place, _)| {
                            let ty = sub_place.ty(body.local_decls(), tcx).ty;
                            !matches!(ty.ref_mutability(), Some(Mutability::Not))
                        })
                    })
                    .copied()
                    .collect::<HashSet<_>>();
            };

            debug!("  Mutated conflicting places: {mutable_conflicts:?}");
            debug!("    with deps {input_location_deps:?}");

            for place in mutable_conflicts.into_iter() {
                state.union_after(
                    all_aliases.normalize(place),
                    &input_location_deps,
                    global_loc.into(),
                );
            }
        }
    }

}

impl<'a, 'tcx, 'g> AnalysisDomain<'tcx> for FlowAnalysis<'a, 'tcx, 'g> {
    type Domain = FlowDomain,
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
                state.insert(
                    self.aliases.normalize(*place),
                    self.location_domain().value(loc).into(),
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
                self.transfer_function(state, mutated, inputs, location, mutation_status, None)
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
                self.transfer_function(state, mutated, inputs, location, mutation_status, None)
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

fn compute_flow_internal<'a, 'tcx, 'g>(
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
            .iter()
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
