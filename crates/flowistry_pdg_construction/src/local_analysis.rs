use std::{borrow::Cow, collections::HashSet, fmt::Display, iter, rc::Rc};

use flowistry::mir::{placeinfo::PlaceInfo, FlowistryInput};
use flowistry_pdg::{CallString, GlobalLocation, RichLocation};
use itertools::Itertools;
use log::{debug, log_enabled, trace, Level};

use rustc_borrowck::consumers::{places_conflict, PlaceConflictBias};
use rustc_errors::DiagCtxtHandle;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        visit::Visitor, AggregateKind, BasicBlock, Body, HasLocalDecls, Location, Operand, Place,
        PlaceElem, Rvalue, Statement, Terminator, TerminatorEdges, TerminatorKind, RETURN_PLACE,
    },
    ty::{GenericArgKind, GenericArgsRef, Instance, TyCtxt, TyKind},
};
use rustc_mir_dataflow::{self as df, fmt::DebugWithContext, Analysis};
use rustc_span::{source_map::Spanned, DesugaringKind, Span};
use rustc_utils::{mir::control_dependencies::ControlDependencies, BodyExt, PlaceExt};

use crate::{
    approximation::ApproximationHandler,
    async_support::*,
    body_cache::CachedBody,
    calling_convention::*,
    graph::{DepEdge, DepNode, PartialGraph, SourceUse, TargetUse},
    mutation::{ModularMutationVisitor, Mutation, Time},
    utils::{self, handle_shims, is_async, is_virtual, try_monomorphize, ShimType},
    CallChangeCallback, CallChanges, CallInfo, InlineMissReason, MemoPdgConstructor, SkipCall,
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
    body_with_facts: &'tcx CachedBody<'tcx>,
    pub(crate) mono_body: Body<'tcx>,
    pub(crate) def_id: DefId,
    pub(crate) place_info: PlaceInfo<'tcx>,
    control_dependencies: ControlDependencies<BasicBlock>,
    pub(crate) body_assignments: utils::BodyAssignments,
    start_loc: FxHashSet<RichLocation>,
}

impl<'tcx, 'a> LocalAnalysis<'tcx, 'a> {
    /// Creates [`GraphConstructor`] for a function resolved as `fn_resolution`
    /// in a given `calling_context`.
    ///
    /// Returns `None`, if we were unable to load the body.
    pub(crate) fn new(
        memo: &'a MemoPdgConstructor<'tcx>,
        root: Instance<'tcx>,
    ) -> LocalAnalysis<'tcx, 'a> {
        let tcx = memo.tcx;
        let def_id = root.def_id();
        let body_with_facts = memo.body_cache.get(def_id);
        let param_env = body_with_facts
            .body()
            .typing_env(tcx)
            .with_post_analysis_normalized(tcx);
        let body = try_monomorphize(
            root,
            tcx,
            param_env,
            body_with_facts.body(),
            tcx.def_span(def_id),
        )
        .unwrap();

        if memo.dump_mir {
            use std::io::Write;
            let path = tcx.def_path_str(def_id) + ".mir";
            let mut f = std::fs::File::create(path.as_str()).unwrap();
            write!(f, "{}", body.to_string(tcx).unwrap()).unwrap();
            debug!("Dumped debug MIR {path}");
        }

        let place_info = PlaceInfo::build(tcx, def_id, body_with_facts);
        let control_dependencies = body.control_dependencies();

        let mut start_loc = FxHashSet::default();
        start_loc.insert(RichLocation::Start);

        let body_assignments = utils::find_body_assignments(&body);

        LocalAnalysis {
            memo,
            root,
            body_with_facts,
            mono_body: body,
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
            &self.mono_body,
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
                    let ctrl_loc = self.mono_body.terminator_loc(dep);
                    let Terminator {
                        kind: TerminatorKind::SwitchInt { discr, .. },
                        source_info,
                    } = self.mono_body.basic_blocks[dep].terminator()
                    else {
                        if blocks_seen.insert(dep) {
                            block_queue.push(dep);
                        }
                        continue;
                    };
                    if matches!(
                        source_info.span.desugaring_kind(),
                        Some(DesugaringKind::Await)
                    ) {
                        // We are dealing with control flow that was introduced
                        // by the "await" state machine. We don't care about
                        // this sine it's possible semantic impact is negligible.
                        continue;
                    }
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
            function: self.def_id,
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
        let place_retyped =
            utils::retype_place(place, self.tcx(), self.body_with_facts.body(), self.def_id);
        self.place_info
            .aliases(place_retyped)
            .iter()
            .map(move |alias| {
                let mut projection = alias.projection.to_vec();
                projection.extend(&place.projection[place_retyped.projection.len()..]);
                let p = Place::make(alias.local, &projection, self.tcx());
                // let t1 = place.ty(&self.body, self.tcx());
                // let t2 = p.ty(&self.body, self.tcx());
                // if !t1.equiv(&t2) {
                //     let p1_str = format!("{place:?}");
                //     let p2_str = format!("{p:?}");
                // let l = p1_str.len().max(p2_str.len());
                //     panic!("Retyping in {} failed to produce an equivalent type.\n  Src {p1_str:l$} : {t1:?}\n  Dst {p2_str:l$} : {t2:?}", self.tcx().def_path_str(self.def_id))
                // }
                p
            })
    }

    pub(crate) fn tcx(&self) -> TyCtxt<'tcx> {
        self.memo.tcx
    }

    pub(crate) fn dcx(&self) -> DiagCtxtHandle<'tcx> {
        self.tcx().dcx()
    }

    /// Returns all nodes `src` such that `src` is:
    /// 1. Part of the value of `input`
    /// 2. The most-recently modified location for `src`
    pub(crate) fn find_data_inputs(
        &self,
        state: &InstructionState<'tcx>,
        input: Place<'tcx>,
    ) -> Vec<DepNode<'tcx>> {
        trace!("Finding inputs for place {input:?}");
        // Include all sources of indirection (each reference in the chain) as relevant places.
        let provenance = input
            .refs_in_projection(&self.mono_body, self.tcx())
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
                        if place.is_indirect() && place.is_arg(&self.mono_body) {
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
                                if new_place.ty(&self.mono_body, self.tcx()).ty.is_box() {
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
                            trace!("Checking conflict status of {place:?} and {alias:?}");
                            places_conflict(
                                self.tcx(),
                                &self.mono_body,
                                place,
                                alias,
                                PlaceConflictBias::Overlap,
                            )
                        }
                    });

                // Special case: if the `alias` is an un-mutated argument, then include it as a conflict
                // coming from the special start location.
                let alias_last_mut = if alias.is_arg(&self.mono_body) {
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
    ) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        let ty = func.ty(&self.mono_body, self.tcx());
        utils::type_as_fn(self.tcx(), ty)
    }

    fn fmt_fn(&self, def_id: DefId) -> String {
        self.tcx().def_path_str(def_id)
    }

    pub(crate) fn determine_call_handling<'b>(
        &'b self,
        location: Location,
        func: Cow<'_, Operand<'tcx>>,
        args: Cow<'b, [Spanned<Operand<'tcx>>]>,
        span: Span,
    ) -> Option<CallHandling<'tcx, 'b>> {
        let tcx = self.tcx();

        trace!(
            "Considering call at {location:?} in {:?}",
            self.tcx().def_path_str(self.def_id)
        );

        let Some((called_def_id, generic_args)) = self.operand_to_def_id(&func) else {
            self.dcx()
                .span_err(span, "Operand is cannot be interpreted as function");
            return None;
        };
        trace!("Resolved call to function: {}", self.fmt_fn(called_def_id));

        // Monomorphize the called function with the known generic_args.
        let typing_env = self
            .body_with_facts
            .body()
            .typing_env(tcx)
            .with_post_analysis_normalized(tcx);
        let Some(mut resolved_fn) =
            utils::try_resolve_function(self.tcx(), called_def_id, typing_env, generic_args)
        else {
            let dynamics = generic_args.iter()
                .flat_map(|g| g.walk())
                .filter(|arg| matches!(arg.unpack(), GenericArgKind::Type(t) if matches!(t.kind(), TyKind::Dynamic(..))))
                .collect::<Box<[_]>>();
            let mut msg = format!(
                "instance resolution for call to function {} failed.",
                tcx.def_path_str(called_def_id)
            );
            if !dynamics.is_empty() {
                use std::fmt::Write;
                write!(msg, " Dynamic arguments ").unwrap();
                let mut first = true;
                for dyn_ in dynamics.iter() {
                    if !first {
                        write!(msg, ", ").unwrap();
                    }
                    first = false;
                    write!(msg, "`{dyn_}`").unwrap();
                }
                write!(
                    msg,
                    " were found.\n\
                    These may have been injected by Paralegal to instantiate generics \n\
                    at the entrypoint (location of #[paralegal::analyze]).\n\
                    A likely reason why this may cause this resolution to fail is if the\n\
                    method or function this attempts to resolve has a `Sized` constraint.\n\
                    Such a constraint can be implicit if this is a type variable in a\n\
                    trait definition and no refutation (`?Sized` constraint) is present."
                )
                .unwrap();
                self.dcx().span_warn(span, msg);
            } else {
                self.dcx().span_err(span, msg);
            }
            return None;
        };

        let call_kind = if let Some((instance, shim_type)) =
            handle_shims(resolved_fn, self.tcx(), typing_env, span)
        {
            resolved_fn = instance;
            CallKind::Indirect {
                shim: Some(shim_type),
            }
        } else {
            self.classify_call_kind(called_def_id, resolved_fn, &args, span)
        };
        let resolved_def_id = resolved_fn.def_id();
        if log_enabled!(Level::Trace) && called_def_id != resolved_def_id {
            let (called, resolved) = (self.fmt_fn(called_def_id), self.fmt_fn(resolved_def_id));
            trace!("  `{called}` monomorphized to `{resolved}`",);
        }

        if let Some(handler) = self.can_approximate_async_functions(resolved_def_id) {
            return Some(CallHandling::ApproxAsyncSM(handler));
        };

        trace!("  Handling call! with kind {}", call_kind);

        // Recursively generate the PDG for the child function.
        let cache_key = resolved_fn;

        let is_cached = self.memo.is_in_cache(cache_key);

        let call_changes = self.call_change_callback().map(|callback| {
            let info = CallInfo {
                callee: resolved_fn,
                call_string: self.make_call_string(location),
                is_cached,
                async_parent: if let CallKind::AsyncPoll(poll) = &call_kind {
                    // Special case for async. We ask for skipping not on the closure, but
                    // on the "async" function that created it. This is needed for
                    // consistency in skipping. Normally, when "poll" is inlined, mutations
                    // introduced by the creator of the future are not recorded and instead
                    // handled here, on the closure. But if the closure is skipped we need
                    // those mutations to occur. To ensure this we always ask for the
                    // "CallChanges" on the creator so that both creator and closure have
                    // the same view of whether they are inlined or "Skip"ped.
                    poll.async_fn_parent
                } else {
                    None
                },
                span,
                arguments: &args,
                caller_body: &self.mono_body,
                param_env: typing_env,
            };
            callback.on_inline(info)
        });

        // Handle async functions at the time of polling, not when the future is created.
        if is_async(tcx, resolved_def_id) {
            trace!("  Bailing because func is async");

            // If a skip was requested then "poll" will not be inlined later so we
            // bail with "None" here and perform the mutations. Otherwise we bail with
            // "Some", knowing that handling "poll" later will handle the mutations.
            return (!matches!(
                &call_changes,
                Some(CallChanges {
                    skip: SkipCall::Skip,
                    ..
                })
            ))
            .then_some(CallHandling::ApproxAsyncFn);
        }

        let (calling_convention, precise) = match call_changes {
            Some(CallChanges {
                skip: SkipCall::Skip,
            }) => {
                trace!("  Bailing because user callback said to bail");
                return None;
            }
            Some(CallChanges {
                skip:
                    SkipCall::Replace {
                        instance,
                        calling_convention,
                    },
            }) => {
                trace!("  Replacing call as instructed by user");
                resolved_fn = instance;
                (calling_convention, false)
            }
            _ => (CallingConvention::from_call_kind(&call_kind, args), true),
        };
        if is_virtual(tcx, resolved_def_id) {
            trace!("  bailing because is unresolvable trait method");
            if let Some(callback) = self.call_change_callback() {
                callback.on_inline_miss(
                    resolved_fn,
                    typing_env,
                    location,
                    self.root,
                    InlineMissReason::TraitMethod,
                    span,
                );
            }
            return None;
        }
        let Some(descriptor) = self.memo.construct_for(resolved_fn) else {
            trace!("  Bailing because of recursion.");
            return None;
        };

        Some(CallHandling::Ready {
            descriptor,
            calling_convention,
            precise,
        })
    }

    /// Attempt to inline a call to a function.
    ///
    /// The return indicates whether we were successfully able to perform the inlining.
    fn handle_call(
        &self,
        state: &mut InstructionState<'tcx>,
        location: Location,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        span: Span,
    ) -> bool {
        // Note: my comments here will use "child" to refer to the callee and
        // "parent" to refer to the caller, since the words are most visually distinct.

        let Some(preamble) =
            self.determine_call_handling(location, Cow::Borrowed(func), Cow::Borrowed(args), span)
        else {
            return false;
        };

        trace!("Call handling is {}", preamble.as_ref());

        let (child_constructor, calling_convention, precise) = match preamble {
            CallHandling::Ready {
                descriptor,
                calling_convention,
                precise,
            } => (descriptor, calling_convention, precise),
            CallHandling::ApproxAsyncFn => {
                // Register a synthetic assignment of `future = (arg0, arg1, ...)`.
                let rvalue = Rvalue::Aggregate(
                    Box::new(AggregateKind::Tuple),
                    IndexVec::from_iter(args.iter().map(|o| o.node.clone())),
                );
                self.modular_mutation_visitor(state)
                    .visit_assign(&destination, &rvalue, location);
                return true;
            }
            CallHandling::ApproxAsyncSM(handler) => {
                handler(
                    self,
                    &mut self.modular_mutation_visitor(state),
                    args,
                    destination,
                    location,
                );
                return true;
            }
        };

        let parentable_dsts = child_constructor.parentable_dsts(|n| n.len() == 1);
        let parent_body = &self.mono_body;

        let place_translator = PlaceTranslator::new(
            self.async_info(),
            self.def_id,
            parent_body,
            self.tcx(),
            destination,
            &calling_convention,
            precise,
        );

        // For each destination node CHILD that is parentable to PLACE,
        // add an edge from CHILD -> PLACE.
        //
        // PRECISION TODO: for a given child place, we only want to connect
        // the *last* nodes in the child function to the parent, not *all* of them.
        trace!("CHILD -> PARENT EDGES:");
        for (child_dst, _) in parentable_dsts {
            if let Some(parent_place) = place_translator.translate_to_parent(child_dst.place) {
                self.apply_mutation(state, location, parent_place);
            }
        }

        true
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

    pub(crate) fn construct_partial(&'a self) -> PartialGraph<'tcx> {
        let mut analysis = self.iterate_to_fixpoint(self.tcx(), self.body_with_facts.body(), None);

        let mut final_state = PartialGraph::new(
            self.generic_args(),
            self.def_id,
            self.mono_body.arg_count,
            self.mono_body.local_decls(),
        );

        analysis.visit_reachable_with(&self.mono_body, &mut final_state);

        let all_returns = self
            .mono_body
            .all_returns()
            .map(|ret| ret.block)
            .collect_vec();
        let mut analysis = analysis.into_results_cursor(&self.mono_body);
        for block in all_returns {
            analysis.seek_to_block_end(block);
            let return_state = analysis.get();
            for (place, locations) in &return_state.last_mutation {
                let ret_kind = if place.local == RETURN_PLACE {
                    TargetUse::Return
                } else if let Some(num) = other_as_arg(*place, &self.mono_body) {
                    TargetUse::MutArg(num)
                } else {
                    continue;
                };
                for location in locations {
                    let src = self.make_dep_node(*place, *location);
                    let dst = self.make_dep_node(*place, RichLocation::End);
                    let edge = DepEdge::data(
                        self.make_call_string(self.mono_body.terminator_loc(block)),
                        SourceUse::Operand,
                        ret_kind,
                    );
                    final_state.edges.insert((src, dst, edge));
                }
            }
        }

        final_state
    }

    /// Determine the type of call-site.
    ///
    /// The error case is if we tried to resolve this as async and failed. We
    /// know it *is* async but we couldn't determine the information needed to
    /// analyze the function, therefore we will have to approximate it.
    fn classify_call_kind<'b>(
        &'b self,
        def_id: DefId,
        resolved_fn: Instance<'tcx>,
        original_args: &'b [Spanned<Operand<'tcx>>],
        span: Span,
    ) -> CallKind<'tcx> {
        match self.try_poll_call_kind(def_id, resolved_fn, original_args) {
            AsyncDeterminationResult::Resolved(r) => r,
            AsyncDeterminationResult::NotAsync => self
                .try_indirect_call_kind(resolved_fn.def_id())
                .unwrap_or(CallKind::Direct),
            AsyncDeterminationResult::Unresolvable(reason) => self.dcx().span_fatal(span, reason),
        }
    }

    fn try_indirect_call_kind(&self, def_id: DefId) -> Option<CallKind<'tcx>> {
        self.tcx()
            .is_closure_like(def_id)
            .then_some(CallKind::Indirect { shim: None })
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

impl<'tcx, 'a> LocalAnalysis<'tcx, 'a> {
    fn handle_terminator(
        &self,
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
            if self.handle_call(
                state,
                location,
                func,
                args,
                *destination,
                terminator.source_info.span,
            ) {
                return;
            }
        }
        // Fallback: call the visitor
        self.terminator_visitor(state, time)
            .visit_terminator(terminator, location)
    }
}

impl<'a, 'tcx> df::Analysis<'tcx> for &'a LocalAnalysis<'tcx, 'a> {
    type Domain = InstructionState<'tcx>;

    const NAME: &'static str = "LocalPdgConstruction";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        InstructionState::default()
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, _state: &mut Self::Domain) {}
    fn apply_primary_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.modular_mutation_visitor(state)
            .visit_statement(statement, location)
    }

    fn apply_primary_terminator_effect<'mir>(
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
    Indirect {
        /// The call takes place via a shim that implements `FnOnce` for a `Fn`
        /// or `FnMut` closure.
        shim: Option<ShimType>,
    },
    /// A poll to an async function, like `f.await`.
    AsyncPoll(AsyncFnPollEnv<'tcx>),
}

impl Display for CallKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Direct => f.write_str("direct")?,
            Self::AsyncPoll(_) => f.write_str("async poll")?,
            Self::Indirect { shim: None } => f.write_str("indirect")?,
            Self::Indirect { shim: Some(shim) } => write!(f, "({} shim)", shim.as_ref())?,
        }
        Ok(())
    }
}

#[derive(strum::AsRefStr)]
pub(crate) enum CallHandling<'tcx, 'a> {
    ApproxAsyncFn,
    Ready {
        calling_convention: CallingConvention<'tcx>,
        descriptor: &'a PartialGraph<'tcx>,
        precise: bool,
    },
    ApproxAsyncSM(ApproximationHandler<'tcx, 'a>),
}

fn other_as_arg<'tcx>(place: Place<'tcx>, body: &Body<'tcx>) -> Option<u8> {
    (body.local_kind(place.local) == rustc_middle::mir::LocalKind::Arg)
        .then(|| place.local.as_u32() as u8 - 1)
}
