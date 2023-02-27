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

pub type FlowResults<'a, 'tcx, 'g> = engine::AnalysisResults<'tcx, FlowAnalysis<'a, 'tcx, 'g>>;

pub type FlowDomainMatrix<'tcx, 'g> = HashMap<GlobalPlace<'tcx, 'g>, HashSet<GlobalLocation<'g>>>;

#[derive(PartialEq, Eq, Clone, Default)]
pub struct FlowDomain<'tcx, 'g> {
    matrix: FlowDomainMatrix<'tcx, 'g>,
    overrides: HashMap<GlobalPlace<'tcx, 'g>, GlobalLocation<'g>>,
}

impl<'tcx, 'g> FlowDomain<'tcx, 'g> {
    fn override_(&mut self, row: GlobalPlace<'tcx, 'g>, at: GlobalLocation<'g>) -> bool {
        let r = self.overrides.insert(row, at);
        if let Some(old) = r {
            if old != at {
                warn!("Duplicate override for key {row:?}, old:{old:?} new:{at:?}");
            }
        }
        r.is_none()
    }

    fn insert(&mut self, k: GlobalPlace<'tcx, 'g>, v: GlobalLocation<'g>) -> bool {
        self.matrix.entry(k).or_default().insert(v)
    }

    fn matrix(&self) -> &FlowDomainMatrix<'tcx, 'g> {
        &self.matrix
    }
    fn matrix_mut<'a>(&mut self) -> &mut FlowDomainMatrix<'tcx, 'g> {
        &mut self.matrix
    }
    fn row<'a>(&'a self, row: GlobalPlace<'tcx, 'g>) -> &HashSet<GlobalLocation<'g>> {
        &self.matrix[&row]
    }
    fn union_after(
        &mut self,
        row: GlobalPlace<'tcx, 'g>,
        _from: &HashSet<GlobalLocation<'g>>,
        at: GlobalLocation<'g>,
    ) -> bool {
        self.override_(row, at)
    }
    fn include(&mut self, row: GlobalPlace<'tcx, 'g>, at: GlobalLocation<'g>) -> bool {
        self.override_(row, at)
    }
    fn merge_subflow(&mut self, other: &Self, gli: GliAt<'g>) {
        for (&k, v) in other.matrix() {
            for &d in v {
                self.insert(gli.relativize_place(k), gli.relativize(d));
            }
        }
    }
}

impl<'tcx, 'g> JoinSemiLattice for FlowDomain<'tcx, 'g> {
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
        state: &mut FlowDomain<'tcx, 'g>,
        mutated: Place<'tcx>,
        inputs: &[(GlobalPlace<'tcx, 'g>, Option<PlaceElem<'tcx>>)],
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
        let global_loc = gli.as_global_location();

        // Clear sub-places of mutated place (if sound to do so)
        if matches!(mutation_status, MutationStatus::Definitely) && mutated_aliases.len() == 1 {
            let mutated_direct = mutated_aliases.iter().next().unwrap();
            for sub in all_aliases.children(*mutated_direct).iter() {
                state
                    .matrix_mut()
                    .remove(&GlobalPlace::from_local(all_aliases.normalize(*sub)));
            }
        }

        let mut input_location_deps = HashSet::default();
        input_location_deps.insert(global_loc);

        let add_deps = |global_place: GlobalPlace<'tcx, 'g>, location_deps: &mut HashSet<GlobalLocation<'g>>| {
            let place = global_place.place;
            let reachable_values = {
                let aliases = match subfn_ana {
                    _ if global_place.is_local() => all_aliases,
                    Some((body_id, ana)) if global_place.location.map(|l| l.function()) == Some(body_id) => &ana.analysis.aliases,
                    _ => panic!(),
                };
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
                let deps = state.row(GlobalPlace::from_local(all_aliases.normalize(*relevant)));
                trace!("    For relevant {relevant:?} for input {place:?} adding deps {deps:?}");
                location_deps.extend(deps.iter());
            }
        };

        // Add deps of mutated to include provenance of mutated pointers
        add_deps(GlobalPlace::from_local(mutated), &mut input_location_deps);

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
                self.gli
                    .globalize_location(body.terminator_loc(block), body_id),
            );

            // Include dependencies of the switch's operand
            let terminator = body.basic_blocks()[block].terminator();
            if let TerminatorKind::SwitchInt { discr, .. } = &terminator.kind {
                if let Some(discr_place) = discr.to_place() {
                    add_deps(GlobalPlace::from_local(discr_place), &mut input_location_deps);
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
                    GlobalPlace::from_local(all_aliases.normalize(child)),
                    global_loc,
                );
            }

            // Then for constructor arguments that were places, add dependencies of those places.
            for (child, deps) in children {
                state.union_after(
                    GlobalPlace::from_local(all_aliases.normalize(child)),
                    &deps,
                    global_loc,
                );
            }

            // Finally add input_location_deps *JUST* to mutated, not conflicts of mutated.
            state.union_after(
                GlobalPlace::from_local(all_aliases.normalize(mutated)),
                &input_location_deps,
                global_loc,
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
                    GlobalPlace::from_local(all_aliases.normalize(place)),
                    &input_location_deps,
                    global_loc,
                );
            }
        }
    }
    fn recurse_into_call(
        &self,
        state: &mut FlowDomain<'tcx, 'g>,
        call: &TerminatorKind<'tcx>,
        location: Location,
    ) -> bool {
        let tcx = self.tcx;
        let (func, parent_args, destination) = match call {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => (func, args, destination),
            _ => unreachable!(),
        };
        debug!("Checking whether can recurse into {func:?}");

        let func = match func.constant() {
            Some(func) => func,
            None => {
                debug!("  Func is not constant");
                return false;
            }
        };

        let def_id = match func.literal.ty().kind() {
            TyKind::FnDef(def_id, _) => def_id,
            _ => {
                debug!("  Func is not a FnDef");
                return false;
            }
        };

        // If a function returns never (fn () -> !) then there are no exit points,
        // so we can't analyze effects on exit
        let fn_sig = tcx.fn_sig(*def_id);
        if fn_sig.skip_binder().output().is_never() {
            debug!("  Func returns never");
            return false;
        }

        let node = match tcx.hir().get_if_local(*def_id) {
            Some(node) => node,
            None => {
                debug!("  Func is not in local crate");
                flowistry::extensions::REACHED_LIBRARY.get(|reached_library| {
                    if let Some(reached_library) = reached_library {
                        *reached_library.borrow_mut() = true;
                    }
                });
                return false;
            }
        };

        let body_id = match node.body_id() {
            Some(body_id) => body_id,
            None => {
                debug!("  Func does not have a BodyId");
                return false;
            }
        };

        let unsafety = tcx.unsafety_check_result(def_id.expect_local());
        if !unsafety.used_unsafe_blocks.is_empty() {
            debug!("  Func contains unsafe blocks");
            return false;
        }

        let parent_arg_places = utils::arg_places(parent_args);
        let any_closure_inputs = parent_arg_places.iter().any(|(_, place)| {
            let ty = place.ty(self.body.local_decls(), tcx).ty;
            ty.walk().any(|arg| match arg.unpack() {
                GenericArgKind::Type(ty) => match ty.kind() {
                    TyKind::Closure(_, substs) => matches!(
                        substs.as_closure().kind(),
                        ClosureKind::FnOnce | ClosureKind::FnMut
                    ),
                    _ => false,
                },
                _ => false,
            })
        });
        if any_closure_inputs {
            debug!("  Func has closure inputs");
            return false;
        }

        let recursive = flowistry::infoflow::BODY_STACK.with(|body_stack| {
            let body_stack = body_stack.borrow();
            body_stack.iter().any(|visited_id| *visited_id == body_id)
        });
        if recursive {
            debug!("  Func is a recursive call");
            return false;
        }

        let body_with_facts = get_body_with_borrowck_facts(tcx, def_id.expect_local());
        let mut recurse_cache = self.recurse_cache.borrow_mut();
        let flow = recurse_cache.entry(body_id).or_insert_with(|| {
            info!("Recursing into {}", tcx.def_path_debug_str(*def_id));
            compute_flow_internal(
                tcx,
                self.gli,
                body_id,
                body_with_facts,
                self.recurse_selector,
            )
        });
        let body = &body_with_facts.simplified_body();

        let mut return_state = FlowDomain::default();
        {
            let return_locs = body
                .basic_blocks()
                .iter_enumerated()
                .filter_map(|(bb, data)| match data.terminator().kind {
                    TerminatorKind::Return => Some(body.terminator_loc(bb)),
                    _ => None,
                });

            for loc in return_locs {
                return_state.join(flow.state_at(loc));
            }
        };

        let translate_child_to_parent =
            |child: Place<'tcx>, mutated: bool| -> Option<Place<'tcx>> {
                if child.local == RETURN_PLACE && child.projection.len() == 0 {
                    if child.ty(body.local_decls(), tcx).ty.is_unit() {
                        return None;
                    }

                    if let Some((dst, _)) = destination {
                        return Some(*dst);
                    }
                }

                if !child.is_arg(body) || (mutated && !child.is_indirect()) {
                    return None;
                }

                // For example, say we're calling f(_5.0) and child = (*_1).1 where
                // .1 is private to parent. Then:
                //    parent_toplevel_arg = _5.0
                //    parent_arg_projected = (*_5.0).1
                //    parent_arg_accessible = (*_5.0)

                let parent_toplevel_arg = parent_arg_places
                    .iter()
                    .find(|(j, _)| child.local.as_usize() - 1 == *j)
                    .map(|(_, place)| place)?;

                let mut projection = parent_toplevel_arg.projection.to_vec();
                let mut ty = parent_toplevel_arg.ty(self.body.local_decls(), tcx);
                let parent_param_env = tcx.param_env(self.def_id);
                log::debug!("Adding child {child:?} to parent {parent_toplevel_arg:?}");
                for elem in child.projection.iter() {
                    ty = ty.projection_ty_core(tcx, parent_param_env, &elem, |_, field, _| {
                        ty.field_ty(tcx, field)
                    });
                    let elem = match elem {
                        ProjectionElem::Field(field, _) => ProjectionElem::Field(field, ty.ty),
                        elem => elem,
                    };
                    projection.push(elem);
                }

                let parent_arg_projected = Place::make(parent_toplevel_arg.local, &projection, tcx);
                Some(parent_arg_projected)
            };

        state.merge_subflow(&return_state, self.gli_at(location));

        for (&child, child_deps) in return_state.matrix().iter() {
            if let Some(parent) = translate_child_to_parent(child.place, true) {
                let was_return = child.is_return_place();
                // > 1 because arguments will always have their synthetic location in their dep set
                let was_mutated = return_state.row(child).len() > 1;
                if !was_mutated && !was_return {
                    continue;
                }

                self.transfer_function(
                    state,
                    parent,
                    &[(child, None)],
                    location,
                    if was_return {
                        MutationStatus::Definitely
                    } else {
                        MutationStatus::Possibly
                    },
                    Some((body_id, flow))
                    
                );
            }
        }

        true
    }
}

impl<'a, 'tcx, 'g> AnalysisDomain<'tcx> for FlowAnalysis<'a, 'tcx, 'g> {
    type Domain = FlowDomain<'tcx, 'g>;
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
                    GlobalPlace::from_local(self.aliases.normalize(*place)),
                    self.gli
                        .globalize_location(*self.location_domain().value(loc), self.body_id()),
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
                let global_inputs = inputs.into_iter().cloned().map(|(place, proj)| (GlobalPlace::from_local(place), proj)).collect::<Vec<_>>();
                self.transfer_function(state, mutated, global_inputs.as_slice(), location, mutation_status, None)
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
        if matches!(terminator.kind, TerminatorKind::Call { .. })
            && self
                .recurse_selector
                .is_selected(self.tcx, &terminator.kind)
            && self.recurse_into_call(state, &terminator.kind, location)
        {
            return;
        }
        ModularMutationVisitor::new(
            &self.aliases,
            |mutated: Place<'tcx>,
             inputs: &[(Place<'tcx>, Option<PlaceElem<'tcx>>)],
             location: Location,
             mutation_status: MutationStatus| {
                let global_inputs = inputs.into_iter().cloned().map(|(place, proj)| (GlobalPlace::from_local(place), proj)).collect::<Vec<_>>();
                self.transfer_function(state, mutated, global_inputs.as_slice(), location, mutation_status, None)
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
