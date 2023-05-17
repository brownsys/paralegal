use std::{borrow::Cow, fmt::Display, rc::Rc};

use crate::{
    ana,
    ir::global_location::{GliAt, GLI},
    rust::{
        mir::{visit::Visitor, *},
        rustc_data_structures::fx::FxHashSet as HashSet,
        rustc_hir::{def_id::DefId, BodyId},
        rustc_mir_dataflow::{self, Analysis, AnalysisDomain, Forward, JoinSemiLattice},
        ty::{self, subst::GenericArgKind},
    },
    utils::{self, AsFnAndArgs, IntoBodyId, SparseMatrix, TyCtxtExt},
    AnalysisCtrl, TyCtxt,
};

use flowistry::{
    extensions::{is_extension_active, MutabilityMode},
    indexed::{impls::LocationDomain, IndexedDomain},
    infoflow::mutation::{ModularMutationVisitor, MutationStatus},
    mir::{
        aliases::Aliases,
        borrowck_facts::CachedSimplifedBodyWithFacts,
        engine,
        utils::{BodyExt, PlaceExt, PlaceRelation},
    },
};

pub use flowistry::mir::control_dependencies::ControlDependencies;

use super::inline::Oracle;

pub type FlowResults<'a, 'tcx, 'g, 'oracle> =
    engine::AnalysisResults<'tcx, FlowAnalysis<'a, 'tcx, 'g, 'oracle>>;

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
        self.matrix().row(&at).into_iter()
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

pub struct FlowAnalysis<'a, 'tcx, 'g, 'oracle> {
    pub tcx: TyCtxt<'tcx>,
    pub def_id: DefId,
    pub body: &'a Body<'tcx>,
    pub control_dependencies: ControlDependencies,
    pub aliases: Aliases<'a, 'tcx>,
    pub gli: GLI<'g>,
    analysis_control: &'static AnalysisCtrl,
    carries_marker: &'oracle dyn Oracle<'tcx, 'oracle>,
    recurse_cache: flowistry::cached::Cache<
        BodyId,
        flowistry::infoflow::FlowResults<'a, 'tcx, flowistry::infoflow::TransitiveFlowDomain<'tcx>>,
    >,
    marker_carrying: utils::RecursionBreakingCache<BodyId, bool>,
}

impl<'a, 'tcx, 'g, 'oracle> FlowAnalysis<'a, 'tcx, 'g, 'oracle> {
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
        carries_marker: &'oracle dyn Oracle<'tcx, 'oracle>,
        analysis_control: &'static AnalysisCtrl,
    ) -> Self {
        FlowAnalysis {
            tcx,
            gli,
            def_id,
            body,
            aliases,
            control_dependencies,
            recurse_cache: flowistry::cached::Cache::default(),
            marker_carrying: Default::default(),
            carries_marker,
            analysis_control,
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
        transitive: bool,
    ) {
        debug!("  Applying mutation to {mutated:?} with inputs {inputs:?}");

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

            debug!("Mutable conflicts {mutable_conflicts:?}");

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
                let normalized = all_aliases.normalize(place);
                // I am unsure if this is the right place to do this. I am using
                // `configurable_of` with `deref_means_disjoint == true` so this
                // propagates
                let relation_to_mutated = PlaceRelation::configurable_of(place, mutated, false);
                if relation_to_mutated == PlaceRelation::Disjoint {
                    debug!("Mutable conflicts {place:?} and {mutated:?} are disjoint");
                };
                if !transitive && relation_to_mutated == PlaceRelation::Super {
                    debug!("  {place:?} was found to be super place of {mutated:?}");
                    let old = state.matrix().row(&normalized).clone();
                    state.union_after(normalized, Cow::Owned(old));
                }
                state.union_after(normalized, Cow::Borrowed(&input_location_deps));
            }
        }
    }

    fn body_carries_marker(&self, bid: BodyId) -> bool {
        *self
            .marker_carrying
            .get(bid, |bid| {
                let body = self.tcx.body_for_body_id(bid).simplified_body();
                body.basic_blocks()
                    .iter()
                    .any(|bbdat| self.fn_carries_marker(body, &bbdat.terminator().kind))
            })
            .unwrap_or(&false)
    }

    fn fn_carries_marker(&self, body: &Body<'tcx>, terminator: &TerminatorKind) -> bool {
        use utils::TyExt;

        if let Ok((defid, args, _)) = terminator.as_fn_and_args() {
            debug!(
                "Checking function {} for markers",
                self.tcx.def_path_debug_str(defid)
            );
            let carries = self.carries_marker.carries_marker(defid);
            let result = if carries {
                debug!("  carries self");
                true
            } else if Some(defid) == self.tcx.lang_items().from_generator_fn() {
                debug!("  is async closure");
                let closure = match args.as_slice() {
                    [Some(p)] => *p,
                    _ => panic!("Expected one non-const closure argument"),
                };
                debug_assert!(closure.projection.is_empty());
                let closure_fn = if let ty::TyKind::Generator(gid, _, _) =
                    body.local_decls[closure.local].ty.kind()
                {
                    *gid
                } else {
                    unreachable!("Expected Generator")
                };
                let map = self.tcx.hir();
                self.body_carries_marker(
                    map.body_owned_by(map.local_def_id_to_hir_id(closure_fn.as_local().unwrap())),
                )
            } else {
                let local_carries = matches!(defid.as_local(), Some(ldid) if
                    self.body_carries_marker(ldid.into_body_id(self.tcx).unwrap()));
                if local_carries {
                    debug!("  body carries");
                }
                let type_carries = self
                    .tcx
                    .fn_sig(defid)
                    .skip_binder()
                    .inputs_and_output
                    .iter()
                    .any(|t| {
                        t.walk().any(|t| match t.unpack() {
                            GenericArgKind::Type(t) => t
                                .defid()
                                .map_or(false, |t| self.carries_marker.carries_marker(t)),
                            _ => false,
                        })
                    });
                if type_carries {
                    debug!("  type carries");
                }
                local_carries | type_carries
            };
            result
        } else {
            false
        }
    }

    fn recurse_into_call(
        &self,
        state: &mut FlowDomain<'tcx>,
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
            ty::TyKind::FnDef(def_id, _) => def_id,
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

        let parent_arg_places = flowistry::mir::utils::arg_places(parent_args);
        let any_closure_inputs = parent_arg_places.iter().any(|(_, place)| {
            let ty = place.ty(self.body.local_decls(), tcx).ty;
            ty.walk().any(|arg| match arg.unpack() {
                ty::subst::GenericArgKind::Type(ty) => match ty.kind() {
                    ty::TyKind::Closure(_, substs) => matches!(
                        substs.as_closure().kind(),
                        ty::ClosureKind::FnOnce | ty::ClosureKind::FnMut
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

        let body_with_facts =
            crate::borrowck_facts::get_body_with_borrowck_facts(tcx, def_id.expect_local());
        let flow = self.recurse_cache.get(body_id, |_| {
            info!("Recursing into {}", tcx.def_path_debug_str(*def_id));
            flowistry::infoflow::compute_flow(tcx, body_id, body_with_facts)
        });
        let body = &body_with_facts.simplified_body();

        let mut return_state = <flowistry::infoflow::TransitiveFlowDomain as flowistry::infoflow::FlowDomain>::from_location_domain(flow.analysis.location_domain());
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
        use flowistry::infoflow::FlowDomain;

        for (child, _) in return_state.matrix().rows() {
            if let Some(parent) = translate_child_to_parent(child, true) {
                let was_return = child.local == RETURN_PLACE;
                // > 1 because arguments will always have their synthetic location in their dep set
                let was_mutated = return_state.row_set(child).len() > 1;
                if !was_mutated && !was_return {
                    continue;
                }

                let child_deps = return_state.row_set(child);
                let parent_deps = return_state
                    .matrix()
                    .rows()
                    .filter(|(_, deps)| child_deps.is_superset(deps))
                    .filter_map(|(row, _)| Some((translate_child_to_parent(row, false)?, None)))
                    .collect::<Vec<_>>();

                debug!(
          "child {child:?} \n  / child_deps {child_deps:?}\n-->\nparent {parent:?}\n   / parent_deps {parent_deps:?}"
        );

                self.transfer_function(state, parent, &parent_deps, location, true);
            }
        }

        true
    }
}

impl<'a, 'tcx, 'g, 'oracle> AnalysisDomain<'tcx> for FlowAnalysis<'a, 'tcx, 'g, 'oracle> {
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

impl<'a, 'tcx, 'g, 'oracle> Analysis<'tcx> for FlowAnalysis<'a, 'tcx, 'g, 'oracle> {
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
             _mutation_status: MutationStatus| {
                self.transfer_function(state, mutated, inputs, location, true)
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
        let is_call = match &terminator.kind {
            TerminatorKind::Call {
                args, destination, ..
            } => {
                if self.analysis_control.avoid_inlining()
                    && !destination.map_or(false, |(d, _)| {
                        d.ty(self.body.local_decls(), self.tcx).ty.is_unit()
                    })
                    && args
                        .iter()
                        .filter_map(Operand::place)
                        .any(|p| !state.matrix().row(&p).is_empty())
                    && !self.fn_carries_marker(self.body, &terminator.kind)
                    && self.recurse_into_call(state, &terminator.kind, location)
                {
                    return;
                }
                true
            }
            _ => false,
        };
        ModularMutationVisitor::new(
            &self.aliases,
            |mutated: Place<'tcx>,
             inputs: &[(Place<'tcx>, Option<PlaceElem<'tcx>>)],
             location: Location,
             _mutation_status: MutationStatus| {
                self.transfer_function(state, mutated, inputs, location, !is_call)
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

pub fn compute_flow_internal<'a, 'tcx, 'g, 'oracle>(
    tcx: TyCtxt<'tcx>,
    gli: GLI<'g>,
    body_id: BodyId,
    body_with_facts: &'a CachedSimplifedBodyWithFacts<'tcx>,
    carries_marker: &'oracle dyn Oracle<'tcx, 'oracle>,
    analysis_control: &'static AnalysisCtrl,
) -> FlowResults<'a, 'tcx, 'g, 'oracle> {
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

            let analysis = FlowAnalysis::new(tcx, gli, def_id, body, aliases, control_dependencies, carries_marker, analysis_control);
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

        body_stack.borrow_mut().pop();

        results
    })
}
