use std::{collections::HashSet, iter, rc::Rc};

use flowistry::mir::placeinfo::PlaceInfo;
use flowistry_pdg::{CallString, GlobalLocation, RichLocation};
use itertools::Itertools;
use log::{debug, log_enabled, trace, Level};

use rustc_borrowck::consumers::{places_conflict, BodyWithBorrowckFacts, PlaceConflictBias};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        visit::Visitor, AggregateKind, BasicBlock, Body, Location, Operand, Place, PlaceElem,
        Rvalue, Statement, Terminator, TerminatorEdges, TerminatorKind, RETURN_PLACE,
    },
    ty::{GenericArg, GenericArgKind, GenericArgsRef, Instance, List, TyCtxt, TyKind},
};
use rustc_mir_dataflow::{self as df, fmt::DebugWithContext, Analysis};

use rustc_span::Span;
use rustc_utils::{
    mir::{borrowck_facts, control_dependencies::ControlDependencies},
    BodyExt, PlaceExt,
};

use crate::{
    approximation::ApproximationHandler,
    async_support::*,
    calling_convention::*,
    construct::{ConstructionErr, WithConstructionErrors},
    graph::{DepEdge, DepNode, PartialGraph, SourceUse, TargetUse},
    mutation::{ModularMutationVisitor, Mutation, Time},
    utils::{self, is_async, is_non_default_trait_method, try_monomorphize},
    Asyncness, CallChangeCallback, CallChanges, CallInfo, InlineMissReason, MemoPdgConstructor,
    SkipCall,
};

#[derive(PartialEq, Eq, Default, Clone, Debug)]
pub(crate) struct InstructionState<'tcx> {
    last_mutation: FxHashMap<Place<'tcx>, FxHashSet<RichLocation>>,
}

impl<C> DebugWithContext<C> for InstructionState<'_> {}

impl<'tcx> df::JoinSemiLattice for InstructionState<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        utils::hashmap_join(
            &mut self.last_mutation,
            &other.last_mutation,
            utils::hashset_join,
        )
    }
}

pub(crate) struct LocalAnalysis<'tcx, 'a> {
    pub(crate) memo: &'a MemoPdgConstructor<'tcx>,
    pub(super) root: Instance<'tcx>,
    body_with_facts: &'tcx BodyWithBorrowckFacts<'tcx>,
    pub(crate) body: Body<'tcx>,
    pub(crate) def_id: LocalDefId,
    pub(crate) place_info: PlaceInfo<'tcx>,
    control_dependencies: ControlDependencies<BasicBlock>,
    pub(crate) body_assignments: utils::BodyAssignments,
    start_loc: FxHashSet<RichLocation>,
}

impl<'tcx, 'a> LocalAnalysis<'tcx, 'a> {
    /// Creates [`GraphConstructor`] for a function resolved as `fn_resolution` in a given `calling_context`.
    pub(crate) fn new(
        memo: &'a MemoPdgConstructor<'tcx>,
        root: Instance<'tcx>,
    ) -> LocalAnalysis<'tcx, 'a> {
        let tcx = memo.tcx;
        let def_id = root.def_id().expect_local();
        let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, def_id);
        let param_env = tcx.param_env_reveal_all_normalized(def_id);
        // let param_env = match &calling_context {
        //     Some(cx) => cx.param_env,
        //     None => ParamEnv::reveal_all(),
        // };
        let body = try_monomorphize(root, tcx, param_env, &body_with_facts.body);

        if memo.dump_mir {
            use std::io::Write;
            let path = tcx.def_path_str(def_id) + ".mir";
            let mut f = std::fs::File::create(path.as_str()).unwrap();
            write!(f, "{}", body.to_string(tcx).unwrap()).unwrap();
            debug!("Dumped debug MIR {path}");
        }

        let place_info = PlaceInfo::build(tcx, def_id.to_def_id(), body_with_facts);
        let control_dependencies = body.control_dependencies();

        let mut start_loc = FxHashSet::default();
        start_loc.insert(RichLocation::Start);

        let body_assignments = utils::find_body_assignments(&body);

        LocalAnalysis {
            memo,
            root,
            body_with_facts,
            body,
            place_info,
            control_dependencies,
            start_loc,
            def_id,
            body_assignments,
        }
    }

    fn make_dep_node(
        &self,
        place: Place<'tcx>,
        location: impl Into<RichLocation>,
    ) -> DepNode<'tcx> {
        DepNode::new(
            place,
            self.make_call_string(location),
            self.tcx(),
            &self.body,
            self.place_info.children(place).iter().any(|p| *p != place),
        )
    }

    /// Returns all pairs of `(src, edge)`` such that the given `location` is control-dependent on `edge`
    /// with input `src`.
    pub(crate) fn find_control_inputs(&self, location: Location) -> Vec<(DepNode<'tcx>, DepEdge)> {
        let mut blocks_seen = HashSet::<BasicBlock>::from_iter(Some(location.block));
        let mut block_queue = vec![location.block];
        let mut out = vec![];
        while let Some(block) = block_queue.pop() {
            if let Some(ctrl_deps) = self.control_dependencies.dependent_on(block) {
                for dep in ctrl_deps.iter() {
                    let ctrl_loc = self.body.terminator_loc(dep);
                    let Terminator {
                        kind: TerminatorKind::SwitchInt { discr, .. },
                        ..
                    } = self.body.basic_blocks[dep].terminator()
                    else {
                        if blocks_seen.insert(dep) {
                            block_queue.push(dep);
                        }
                        continue;
                    };
                    let Some(ctrl_place) = discr.place() else {
                        continue;
                    };
                    let at = self.make_call_string(ctrl_loc);
                    let src = self.make_dep_node(ctrl_place, ctrl_loc);
                    let edge = DepEdge::control(at, SourceUse::Operand, TargetUse::Assign);
                    out.push((src, edge));
                }
            }
        }
        out
    }

    fn call_change_callback(&self) -> Option<&dyn CallChangeCallback<'tcx>> {
        self.memo.call_change_callback.as_ref().map(Rc::as_ref)
    }

    pub(crate) fn async_info(&self) -> &AsyncInfo {
        &self.memo.async_info
    }

    pub(crate) fn make_call_string(&self, location: impl Into<RichLocation>) -> CallString {
        CallString::single(GlobalLocation {
            function: self.root.def_id(),
            location: location.into(),
        })
    }

    /// Returns the aliases of `place`. See [`PlaceInfo::aliases`] for details.
    pub(crate) fn aliases(&'a self, place: Place<'tcx>) -> impl Iterator<Item = Place<'tcx>> + 'a {
        // MASSIVE HACK ALERT:
        // The issue is that monomorphization erases regions, due to how it's implemented in rustc.
        // However, Flowistry's alias analysis uses regions to figure out aliases.
        // To workaround this incompatibility, when we receive a monomorphized place, we try to
        // recompute its type in the context of the original region-containing body as far as possible.
        //
        // For example, say _2: (&'0 impl Foo,) in the original body and _2: (&(i32, i32),) in the monomorphized body.
        // Say we ask for aliases (*(_2.0)).0. Then we will retype ((*_2.0).0).0 and receive back (*_2.0: &'0 impl Foo).
        // We can ask for the aliases in the context of the original body, receiving e.g. {_1}.
        // Then we reproject the aliases with the remaining projection, to create {_1.0}.
        //
        // This is a massive hack bc it's inefficient and I'm not certain that it's sound.
        let place_retyped = utils::retype_place(
            place,
            self.tcx(),
            &self.body_with_facts.body,
            self.def_id.to_def_id(),
        );
        self.place_info.aliases(place_retyped).iter().map(|alias| {
            let mut projection = alias.projection.to_vec();
            projection.extend(&place.projection[place_retyped.projection.len()..]);
            Place::make(alias.local, &projection, self.tcx())
        })
    }

    pub(crate) fn tcx(&self) -> TyCtxt<'tcx> {
        self.memo.tcx
    }

    /// Returns all nodes `src` such that `src` is:
    /// 1. Part of the value of `input`
    /// 2. The most-recently modified location for `src`
    pub(crate) fn find_data_inputs(
        &self,
        state: &InstructionState<'tcx>,
        input: Place<'tcx>,
    ) -> Vec<DepNode<'tcx>> {
        // Include all sources of indirection (each reference in the chain) as relevant places.
        let provenance = input
            .refs_in_projection()
            .map(|(place_ref, _)| Place::from_ref(place_ref, self.tcx()));
        let inputs = iter::once(input).chain(provenance);

        inputs
            // **POINTER-SENSITIVITY:**
            // If `input` involves indirection via dereferences, then resolve it to the direct places it could point to.
            .flat_map(|place| self.aliases(place))
            .flat_map(|alias| {
                // **FIELD-SENSITIVITY:**
                // Find all places that have been mutated which conflict with `alias.`
                let conflicts = state
                    .last_mutation
                    .iter()
                    .map(|(k, locs)| (*k, locs))
                    .filter(move |(place, _)| {
                        if place.is_indirect() && place.is_arg(&self.body) {
                            // HACK: `places_conflict` seems to consider it a bug is `borrow_place`
                            // includes a dereference, which should only happen if `borrow_place`
                            // is an argument. So we special case that condition and just compare for local equality.
                            //
                            // TODO: this is not field-sensitive!
                            place.local == alias.local
                        } else {
                            let mut place = *place;
                            if let Some((PlaceElem::Deref, rest)) = place.projection.split_last() {
                                let mut new_place = place;
                                new_place.projection = self.tcx().mk_place_elems(rest);
                                if new_place.ty(&self.body, self.tcx()).ty.is_box() {
                                    if new_place.is_indirect() {
                                        // TODO might be unsound: We assume that if
                                        // there are other indirections in here,
                                        // there is an alias that does not have
                                        // indirections in it.
                                        return false;
                                    }
                                    place = new_place;
                                }
                            }
                            places_conflict(
                                self.tcx(),
                                &self.body,
                                place,
                                alias,
                                PlaceConflictBias::Overlap,
                            )
                        }
                    });

                // Special case: if the `alias` is an un-mutated argument, then include it as a conflict
                // coming from the special start location.
                let alias_last_mut = if alias.is_arg(&self.body) {
                    Some((alias, &self.start_loc))
                } else {
                    None
                };

                // For each `conflict`` last mutated at the locations `last_mut`:
                conflicts
                    .chain(alias_last_mut)
                    .flat_map(|(conflict, last_mut_locs)| {
                        // For each last mutated location:
                        last_mut_locs.iter().map(move |last_mut_loc| {
                            // Return <CONFLICT> @ <LAST_MUT_LOC> as an input node.
                            self.make_dep_node(conflict, *last_mut_loc)
                        })
                    })
            })
            .collect()
    }

    pub(crate) fn find_outputs(
        &self,
        mutated: Place<'tcx>,
        location: Location,
    ) -> Vec<(Place<'tcx>, DepNode<'tcx>)> {
        // **POINTER-SENSITIVITY:**
        // If `mutated` involves indirection via dereferences, then resolve it to the direct places it could point to.
        let aliases = self.aliases(mutated).collect_vec();

        // **FIELD-SENSITIVITY:** we do NOT deal with fields on *writes* (in this function),
        // only on *reads* (in `add_input_to_op`).

        // For each mutated `dst`:
        aliases
            .iter()
            .map(|dst| {
                // Create a destination node for (DST @ CURRENT_LOC).
                (*dst, self.make_dep_node(*dst, location))
            })
            .collect()
    }

    /// Updates the last-mutated location for `dst` to the given `location`.
    fn apply_mutation(
        &self,
        state: &mut InstructionState<'tcx>,
        location: Location,
        mutated: Place<'tcx>,
    ) {
        self.find_outputs(mutated, location)
            .into_iter()
            .for_each(|(dst, _)| {
                // Create a destination node for (DST @ CURRENT_LOC).

                // Clear all previous mutations.
                let dst_mutations = state.last_mutation.entry(dst).or_default();
                dst_mutations.clear();

                // Register that `dst` is mutated at the current location.
                dst_mutations.insert(RichLocation::Location(location));
            })
    }

    /// Resolve a function [`Operand`] to a specific [`DefId`] and generic arguments if possible.
    pub(crate) fn operand_to_def_id(
        &self,
        func: &Operand<'tcx>,
    ) -> Option<(DefId, &'tcx List<GenericArg<'tcx>>)> {
        let ty = func.ty(&self.body, self.tcx());
        utils::type_as_fn(self.tcx(), ty)
    }

    fn fmt_fn(&self, def_id: DefId) -> String {
        self.tcx().def_path_str(def_id)
    }

    pub(crate) fn determine_call_handling<'b>(
        &'b self,
        location: Location,
        func: &Operand<'tcx>,
        args: &'b [Operand<'tcx>],
        span: Span,
    ) -> Result<Option<CallHandling<'tcx, 'b>>, Vec<ConstructionErr<'tcx>>> {
        let tcx = self.tcx();

        let (called_def_id, generic_args) = self
            .operand_to_def_id(func)
            .ok_or_else(|| vec![ConstructionErr::operand_is_not_function_type(func)])?;
        trace!("Resolved call to function: {}", self.fmt_fn(called_def_id));

        // Monomorphize the called function with the known generic_args.
        let param_env = tcx.param_env_reveal_all_normalized(self.def_id);
        let Some(resolved_fn) =
            utils::try_resolve_function(self.tcx(), called_def_id, param_env, generic_args)
        else {
            if let Some(d) = generic_args.iter().find(|arg| matches!(arg.unpack(), GenericArgKind::Type(t) if matches!(t.kind(), TyKind::Dynamic(..)))) {
                self.tcx().sess.span_warn(self.tcx().def_span(called_def_id), format!("could not resolve instance due to dynamic argument: {d:?}"));
                return Ok(None);
            } else {
                return Err(
                vec![ConstructionErr::instance_resolution_failed(
                    called_def_id,
                    generic_args,
                    span
                )]);
            }
        };
        trace!("resolved to instance {resolved_fn:?}");
        let resolved_def_id = resolved_fn.def_id();
        if log_enabled!(Level::Trace) && called_def_id != resolved_def_id {
            let (called, resolved) = (self.fmt_fn(called_def_id), self.fmt_fn(resolved_def_id));
            trace!("  `{called}` monomorphized to `{resolved}`",);
        }

        if is_non_default_trait_method(tcx, resolved_def_id).is_some() {
            trace!("  bailing because is unresolvable trait method");
            return Ok(None);
        }

        if let Some(handler) = self.can_approximate_async_functions(resolved_def_id) {
            return Ok(Some(CallHandling::ApproxAsyncSM(handler)));
        };

        let call_kind = match self.classify_call_kind(called_def_id, resolved_def_id, args, span) {
            Ok(cc) => cc,
            Err(async_err) => {
                return Err(vec![async_err]);
            }
        };

        let calling_convention = CallingConvention::from_call_kind(&call_kind, args);

        trace!(
            "  Handling call! with kind {}",
            match &call_kind {
                CallKind::Direct => "direct",
                CallKind::Indirect => "indirect",
                CallKind::AsyncPoll { .. } => "async poll",
            }
        );

        // Recursively generate the PDG for the child function.

        let cache_key = resolved_fn;

        let is_cached = self.memo.is_in_cache(cache_key);

        let call_changes = self.call_change_callback().map(|callback| {
            let info = CallInfo {
                callee: resolved_fn,
                call_string: self.make_call_string(location),
                is_cached,
                async_parent: if let CallKind::AsyncPoll(resolution, _loc, _) = call_kind {
                    // Special case for async. We ask for skipping not on the closure, but
                    // on the "async" function that created it. This is needed for
                    // consistency in skipping. Normally, when "poll" is inlined, mutations
                    // introduced by the creator of the future are not recorded and instead
                    // handled here, on the closure. But if the closure is skipped we need
                    // those mutations to occur. To ensure this we always ask for the
                    // "CallChanges" on the creator so that both creator and closure have
                    // the same view of whether they are inlined or "Skip"ped.
                    Some(resolution)
                } else {
                    None
                },
            };
            callback.on_inline(info)
        });

        // Handle async functions at the time of polling, not when the future is created.
        if is_async(tcx, resolved_def_id) {
            trace!("  Bailing because func is async");

            // If a skip was requested then "poll" will not be inlined later so we
            // bail with "None" here and perform the mutations. Otherwise we bail with
            // "Some", knowing that handling "poll" later will handle the mutations.
            return Ok((!matches!(
                &call_changes,
                Some(CallChanges {
                    skip: SkipCall::Skip,
                    ..
                })
            ))
            .then_some(CallHandling::ApproxAsyncFn));
        }

        if matches!(
            call_changes,
            Some(CallChanges {
                skip: SkipCall::Skip,
                ..
            })
        ) {
            trace!("  Bailing because user callback said to bail");
            return Ok(None);
        }
        let Some(descriptor) = self.memo.construct_for(cache_key)? else {
            trace!("  Bailing because cache lookup {cache_key} failed");
            return Ok(None);
        };
        Ok(Some(CallHandling::Ready {
            descriptor,
            calling_convention,
        }))
    }

    /// Attempt to inline a call to a function.
    ///
    /// The return indicates whether we were successfully able to perform the inlining.
    fn handle_call(
        &self,
        state: &mut InstructionState<'tcx>,
        location: Location,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        destination: Place<'tcx>,
        span: Span,
    ) -> Result<bool, Vec<ConstructionErr<'tcx>>> {
        // Note: my comments here will use "child" to refer to the callee and
        // "parent" to refer to the caller, since the words are most visually distinct.

        let Some(preamble) = self.determine_call_handling(location, func, args, span)? else {
            return Ok(false);
        };

        trace!("Call handling is {}", preamble.as_ref());

        let (child_constructor, calling_convention) = match preamble {
            CallHandling::Ready {
                descriptor,
                calling_convention,
            } => (descriptor, calling_convention),
            CallHandling::ApproxAsyncFn => {
                // Register a synthetic assignment of `future = (arg0, arg1, ...)`.
                let rvalue = Rvalue::Aggregate(
                    Box::new(AggregateKind::Tuple),
                    IndexVec::from_iter(args.iter().cloned()),
                );
                self.modular_mutation_visitor(state)
                    .visit_assign(&destination, &rvalue, location);
                return Ok(true);
            }
            CallHandling::ApproxAsyncSM(handler) => {
                handler(
                    self,
                    &mut self.modular_mutation_visitor(state),
                    args,
                    destination,
                    location,
                );
                return Ok(true);
            }
        };

        let parentable_dsts = child_constructor.parentable_dsts();
        let parent_body = &self.body;
        let translate_to_parent = |child: Place<'tcx>| -> Option<Place<'tcx>> {
            calling_convention.translate_to_parent(
                child,
                self.async_info(),
                self.tcx(),
                parent_body,
                self.def_id.to_def_id(),
                destination,
            )
        };

        // For each destination node CHILD that is parentable to PLACE,
        // add an edge from CHILD -> PLACE.
        //
        // PRECISION TODO: for a given child place, we only want to connect
        // the *last* nodes in the child function to the parent, not *all* of them.
        trace!("CHILD -> PARENT EDGES:");
        for (child_dst, _) in parentable_dsts {
            if let Some(parent_place) = translate_to_parent(child_dst.place) {
                self.apply_mutation(state, location, parent_place);
            }
        }

        Ok(true)
    }

    fn modular_mutation_visitor<'b: 'a>(
        &'b self,
        state: &'a mut InstructionState<'tcx>,
    ) -> ModularMutationVisitor<'b, 'tcx, impl FnMut(Location, Mutation<'tcx>) + 'b> {
        ModularMutationVisitor::new(
            &self.place_info,
            move |location, mutation: Mutation<'tcx>| {
                self.apply_mutation(state, location, mutation.mutated)
            },
        )
    }

    pub(super) fn generic_args(&self) -> GenericArgsRef<'tcx> {
        self.root.args
    }

    pub(crate) fn construct_partial(
        &'a self,
    ) -> Result<PartialGraph<'tcx>, Vec<ConstructionErr<'tcx>>> {
        if let Some(g) = self.try_handle_as_async()? {
            return Ok(g);
        }

        let mut analysis = WithConstructionErrors::new(self)
            .into_engine(self.tcx(), &self.body)
            .iterate_to_fixpoint();

        if !analysis.analysis.errors.is_empty() {
            return Err(analysis.analysis.errors.into_iter().collect());
        }

        let mut final_state = WithConstructionErrors::new(PartialGraph::new(
            Asyncness::No,
            self.generic_args(),
            self.def_id.to_def_id(),
            self.body.arg_count,
        ));

        analysis.visit_reachable_with(&self.body, &mut final_state);

        let mut final_state = final_state.into_result()?;

        let all_returns = self.body.all_returns().map(|ret| ret.block).collect_vec();
        let mut analysis = analysis.into_results_cursor(&self.body);
        for block in all_returns {
            analysis.seek_to_block_end(block);
            let return_state = analysis.get();
            for (place, locations) in &return_state.last_mutation {
                let ret_kind = if place.local == RETURN_PLACE {
                    TargetUse::Return
                } else if let Some(num) = other_as_arg(*place, &self.body) {
                    TargetUse::MutArg(num)
                } else {
                    continue;
                };
                for location in locations {
                    let src = self.make_dep_node(*place, *location);
                    let dst = self.make_dep_node(*place, RichLocation::End);
                    let edge = DepEdge::data(
                        self.make_call_string(self.body.terminator_loc(block)),
                        SourceUse::Operand,
                        ret_kind,
                    );
                    final_state.edges.insert((src, dst, edge));
                }
            }
        }

        Ok(final_state)
    }

    /// Determine the type of call-site.
    ///
    /// The error case is if we tried to resolve this as async and failed. We
    /// know it *is* async but we couldn't determine the information needed to
    /// analyze the function, therefore we will have to approximate it.
    fn classify_call_kind<'b>(
        &'b self,
        def_id: DefId,
        resolved_def_id: DefId,
        original_args: &'b [Operand<'tcx>],
        span: Span,
    ) -> Result<CallKind<'tcx>, ConstructionErr<'tcx>> {
        match self.try_poll_call_kind(def_id, original_args, span) {
            AsyncDeterminationResult::Resolved(r) => Ok(r),
            AsyncDeterminationResult::NotAsync => Ok(self
                .try_indirect_call_kind(resolved_def_id)
                .unwrap_or(CallKind::Direct)),
            AsyncDeterminationResult::Unresolvable(reason) => Err(reason),
        }
    }

    fn try_indirect_call_kind(&self, def_id: DefId) -> Option<CallKind<'tcx>> {
        self.tcx().is_closure(def_id).then_some(CallKind::Indirect)
    }

    fn terminator_visitor<'b: 'a>(
        &'b self,
        state: &'b mut InstructionState<'tcx>,
        time: Time,
    ) -> ModularMutationVisitor<'b, 'tcx, impl FnMut(Location, Mutation<'tcx>) + 'b> {
        let mut vis = self.modular_mutation_visitor(state);
        vis.set_time(time);
        vis
    }
}

impl<'tcx, 'a> WithConstructionErrors<'tcx, &'_ LocalAnalysis<'tcx, 'a>> {
    fn handle_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        state: &mut InstructionState<'tcx>,
        location: Location,
        time: Time,
    ) {
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            match self.inner.handle_call(
                state,
                location,
                func,
                args,
                *destination,
                terminator.source_info.span,
            ) {
                Err(e) => {
                    self.errors.extend(e);
                }
                Ok(false) => {
                    trace!("Terminator {:?} failed the preamble", terminator.kind);
                }
                Ok(true) => return,
            }
        }
        // Fallback: call the visitor
        self.inner
            .terminator_visitor(state, time)
            .visit_terminator(terminator, location)
    }
}

impl<'tcx, 'a> df::AnalysisDomain<'tcx>
    for WithConstructionErrors<'tcx, &'a LocalAnalysis<'tcx, 'a>>
{
    type Domain = InstructionState<'tcx>;

    const NAME: &'static str = "LocalPdgConstruction";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        InstructionState::default()
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, _state: &mut Self::Domain) {}
}

impl<'a, 'tcx> df::Analysis<'tcx> for WithConstructionErrors<'tcx, &'a LocalAnalysis<'tcx, 'a>> {
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.inner
            .modular_mutation_visitor(state)
            .visit_statement(statement, location)
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.handle_terminator(terminator, state, location, Time::Unspecified);
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: rustc_middle::mir::CallReturnPlaces<'_, 'tcx>,
    ) {
    }
}

pub enum CallKind<'tcx> {
    /// A standard function call like `f(x)`.
    Direct,
    /// A call to a function variable, like `fn foo(f: impl Fn()) { f() }`
    Indirect,
    /// A poll to an async function, like `f.await`.
    AsyncPoll(Instance<'tcx>, Location, Place<'tcx>),
}

#[derive(strum::AsRefStr)]
pub(crate) enum CallHandling<'tcx, 'a> {
    ApproxAsyncFn,
    Ready {
        calling_convention: CallingConvention<'tcx, 'a>,
        descriptor: &'a PartialGraph<'tcx>,
    },
    ApproxAsyncSM(ApproximationHandler<'tcx, 'a>),
}

fn other_as_arg<'tcx>(place: Place<'tcx>, body: &Body<'tcx>) -> Option<u8> {
    (body.local_kind(place.local) == rustc_middle::mir::LocalKind::Arg)
        .then(|| place.local.as_u32() as u8 - 1)
}
