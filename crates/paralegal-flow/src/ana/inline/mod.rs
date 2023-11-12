//! The [`Inliner`]. The 30s summary of what this does is
//! 1. It starts from single-procedure analyses ([`regal::Body`])
//! 2. Turns them into graphs ([`ProcedureGraph`])
//! 3. Turns locations into global locations in both the graph and in the
//!    equations ([`InlinedGraph`])
//! 4. Inlines callees that are (un)marked. In the graphs the nodes are are
//!    replaced by the callee graph, reconnecting incoming and outgoing edges at
//!    the boundary. Callee locations are relativized ([`GliAt::relativize`]).
//!    Callee equations also have the bases rewritten
//!    ([`Inliner::relativize_eqs`]) before being added to the caller equations.
//! 5. Use the equations from place analysis prune edges
//!    ([`InlinedGraph::prune_impossible_edges`]) using the accumulated set of
//!    equations

use std::fmt::Write;

use crate::{
    ana::algebra::{self, Operator, Term},
    hir::def_id::DefId,
    hir::LanguageItems,
    ir::{
        flows::CallOnlyFlow,
        regal::{self, SimpleLocation},
        GlobalLocation, GlobalLocationS,
    },
    mir,
    mir::Location,
    rustc_ast::Mutability,
    rustc_target::abi::FieldIdx,
    ty,
    utils::{
        body_name_pls, dump_file_pls, time, write_sep, DisplayViaDebug, FnResolution, Print,
        RecursionBreakingCache, Spanned, TyCtxtExt,
    },
    AnalysisCtrl, DumpArgs, Either, HashMap, HashSet, MarkerCtx, Span, Symbol, TyCtxt,
};

use rustc_utils::cache::Cache;

mod graph;
mod judge;

pub use graph::{
    add_weighted_edge, ArgNum, Edge, EdgeType, Equation, Equations, GlobalLocal, GraphImpl,
    InlinedGraph, Node,
};

use petgraph::{
    prelude as pg,
    visit::{EdgeRef, IntoNodeReferences},
};

pub use judge::InlineJudge;

type StdNode<'tcx> = Node<(GlobalLocation, FnResolution<'tcx>)>;

type EdgeSet<'tcx> = HashSet<(StdNode<'tcx>, StdNode<'tcx>)>;

impl<'tcx> Inliner<'tcx> {
    fn edge_has_been_pruned_before(from: StdNode<'tcx>, to: StdNode<'tcx>) -> bool {
        match (to, from) {
            (SimpleLocation::Call(c1), SimpleLocation::Call(c2)) => {
                c1.0.outermost() == c2.0.outermost()
            }
            (SimpleLocation::Call(c), _) | (_, SimpleLocation::Call(c)) => c.0.is_at_root(),
            _ => true,
        }
    }

    fn find_prunable_edges(graph: &InlinedGraph<'tcx>) -> EdgeSet<'tcx> {
        let graph = &graph.graph;
        graph
            .all_edges()
            .filter_map(|(from, to, _)| {
                (!Inliner::edge_has_been_pruned_before(from, to)).then_some((from, to))
            })
            .collect()
    }

    /// For each edge in this graph query the set of equations to determine if
    /// it is memory-plausible e.g. if there exists an argument `a` to the
    /// target and a return `r` from the source such that either `a` can be
    /// reached from `r` or `r` can be reached from `a`.
    ///
    /// The simples example is where `r == a` a more complex example could be
    /// that `r = *a.foo`.
    fn prune_impossible_edges(
        &self,
        graph: &mut InlinedGraph<'tcx>,
        name: Symbol,
        edges_to_prune: &EdgeSet<'tcx>,
        instance: FnResolution<'tcx>,
    ) {
        if edges_to_prune.is_empty() {
            return;
        }
        let tcx: TyCtxt<'tcx> = self.tcx;
        time(&format!("Edge Pruning for {name}"), || {
            let InlinedGraph {
                graph, equations, ..
            } = graph;
            info!(
                "Have {} equations for pruning {} edges",
                equations.len(),
                edges_to_prune
                    .iter()
                    .filter_map(|&(a, b)| Some(graph.edge_weight(a, b)?.count()))
                    .count()
            );

            debug!(
                "{}",
                Print(|f| {
                    for eq in equations.iter() {
                        writeln!(f, "{eq}")?;
                    }
                    Ok(())
                })
            );

            let locals_graph =
                algebra::graph::Graph::new(equations, DisplayViaDebug(instance.def_id()));
            if self.dbg_ctrl.dump_locals_graph() {
                let f = dump_file_pls(
                    self.tcx,
                    instance.def_id().expect_local(),
                    "locals-graph.gv",
                )
                .unwrap();
                locals_graph.dump(f, |_| false, |_| false);
            }

            for &(from, to) in edges_to_prune {
                if let Some(weight) = graph.edge_weight_mut(from, to) {
                    for idx in weight.into_iter_data() {
                        let is_start = self.node_to_match_global_local(to);
                        let is_target = self.node_to_match_global_local(from);
                        let is_reachable = locals_graph.reachable(is_start, is_target);

                        if let Some((_visited, t)) = is_reachable {
                            debug!(
                                "Found {from} -> {to} to be reachable via {}",
                                Print(|fmt| { algebra::display_term_pieces(fmt, &t, &0_usize) })
                            );
                        } else {
                            debug!("Found unreproducible edge {from} -> {to} (idx {idx})");
                            weight.remove_type(EdgeType::Data(idx));
                        }
                    }
                    if weight.is_empty() {
                        graph.remove_edge(from, to);
                    }
                }
            }
        })
    }

    fn node_to_match_global_local<'a, T>(
        &'a self,
        node: SimpleLocation<(GlobalLocation, T)>,
    ) -> impl Fn(GlobalLocal) -> bool + 'a {
        match node {
            Node::Argument(a) => Box::new(move |candidate: GlobalLocal| {
                candidate.location().is_none() && candidate.local.as_usize() == a.as_usize() + 1
            }) as Box<dyn Fn(GlobalLocal) -> bool>,
            Node::Return => Box::new(|candidate: GlobalLocal| {
                candidate.location().is_none() && candidate.local == mir::RETURN_PLACE
            }),
            Node::Call((location, _)) => {
                let call = self.get_call(location);
                let parent = location.parent();
                Box::new(move |candidate: GlobalLocal| {
                    candidate.location() == parent
                        && call
                            .argument_locals()
                            .chain(call.return_to.into_iter())
                            .any(|l| l == candidate.local)
                })
            }
        }
    }
}

/// `None` values indicate that the requested `DefId` could not be analyzed,
/// usually because it is a trait method resulting from a use of `dyn`.
type BodyCache<'tcx> = Cache<DefId, Option<regal::Body<'tcx, DisplayViaDebug<Location>>>>;

/// Essentially just a bunch of caches of analyses.
pub struct Inliner<'tcx> {
    /// Memoized graphs created from single-procedure analyses
    base_memo: BodyCache<'tcx>,
    /// Memoized graphs that have all their callees inlined. Unlike `base_memo`
    /// this has to be recursion breaking, since a function may call itself
    /// (possibly transitively).
    inline_memo: RecursionBreakingCache<FnResolution<'tcx>, Option<InlinedGraph<'tcx>>>,
    tcx: TyCtxt<'tcx>,
    ana_ctrl: &'static AnalysisCtrl,
    dbg_ctrl: &'static DumpArgs,
    marker_carrying: InlineJudge<'tcx>,
}

fn is_part_of_async_desugar<'tcx, L: Copy + Ord + std::hash::Hash + std::fmt::Display>(
    tcx: TyCtxt<'tcx>,
    node: Node<(L, FnResolution<'tcx>)>,
    graph: &GraphImpl<'tcx, L>,
) -> Option<&'static [algebra::Operator<DisplayViaDebug<FieldIdx>>]> {
    const POLL_FN_WRAP: &[Operator<DisplayViaDebug<FieldIdx>>] = &[
        Operator::Downcast(0),
        Operator::MemberOf(DisplayViaDebug(FieldIdx::from_usize(0))),
    ];

    let lang_items = tcx.lang_items();
    // We use `?` here because if any of these functions aren't defined we can
    // just abort.
    let mut seen: [(_, &'static [_], bool); 3] = [
        (lang_items.get_context_fn()?, &[] as &[_], false),
        (
            lang_items
                .into_future_fn()
                .and_then(|f| tcx.trait_of_item(f))?,
            &[],
            false,
        ),
        // I used to add a
        // algebra::Operator::MemberOf(mir::Field::from_usize(0).into())
        // here as well, but while that is technically correct in terms
        // of what this function does, the new encoding for `poll`
        // strips that away before calling the closure, so now I just
        // don't. Probably cleaner would be to change the wrapping for
        // `poll` but I'm lazy
        (
            lang_items.new_unchecked_fn()?,
            &[algebra::Operator::RefOf],
            false,
        ),
    ];
    let mut poll_fn_seen = false;
    let mut queue = vec![node];
    let mut iterations = 0;
    let mut wrap_needed = None;

    // This complex abomination does a few things at once. Starting from the
    // given node it explores the neighbors in turn to see if, fanning out, we
    // find the entire pattern (all functions from `seen` *and* a `poll` style
    // function).
    //
    // It tracks which functions it has seen by setting the booleans in `seen`
    // to true. No node is visited twice. We also have `wrap_needed` which is
    // set on the first iteration to the wrapping value stored for that
    // function. The wrap is a projection in our algebra that encapsulates the
    // behavior of the `node` (which will be replaced by this "algebraic
    // interpretation").
    //
    // Dangers: A `poll` style function here is just matched as some closure. In
    // theory it should be a special closure with a particular type. However
    // since we match on the entire pattern only a function that is surrounded
    // by all other async-desugaring operators would ever be considered
    // appropriate here so it is very unlikely to trigger for any non-async
    // desugared closure. Perhaps important to mention here too is that in the
    // pattern we look for the closure is in the middle of the other nodes. So
    // if by chance a closure in the periphery of such a pattern started to
    // match, the search over the pattern should be abandoned and `None` returned
    // as soon as the "actual" `poll` style closure is encountered (because the
    // `poll` style function would already be marked as seen).

    while let Some(node) = queue.pop() {
        iterations += 1;
        if let SimpleLocation::Call((_, inst)) = node
            && let maybe_resolved_trait = tcx.impl_of_method(inst.def_id()).and_then(|impl_| tcx.trait_id_of_impl(impl_))
            && let Some((wrap, was_seen)) = seen
                .iter_mut()
                .find(|(k, _, _)| *k == inst.def_id() || Some(*k) == maybe_resolved_trait)
                .map(|(_, w, t)| (*w, t))
                .or_else(|| {
                    tcx.is_closure(inst.def_id()).then_some((POLL_FN_WRAP, &mut poll_fn_seen))
                })
            && !*was_seen
        {
            wrap_needed.get_or_insert(wrap);
            *was_seen = true;
            queue.extend(graph.neighbors_directed(node, petgraph::Direction::Incoming));
            queue.extend(graph.neighbors_directed(node, petgraph::Direction::Outgoing))
        } else if iterations > 0 {
            debug!("{node} did not belong to pattern");
        }
    }
    if poll_fn_seen || seen.iter().any(|v| v.2) {
        debug!(
            "Saw some async desugar pattern around node {node} in {iterations} \
               iterations: \n   poll: {poll_fn_seen} {}",
            Print(|f| write_sep(f, "", seen, |elem, f| write!(
                f,
                "\n   {:?}: {}",
                elem.0, elem.2
            )))
        )
    }
    (poll_fn_seen && seen.iter().all(|v| v.2))
        .then_some(wrap_needed)
        .flatten()
}

enum InlineAction<'tcx> {
    SimpleInline(FnResolution<'tcx>),
    Drop(DropAction),
}

type DropAction = Vec<algebra::Operator<DisplayViaDebug<mir::Field>>>;

impl<'tcx> Inliner<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        marker_ctx: MarkerCtx<'tcx>,
        ana_ctrl: &'static AnalysisCtrl,
        dbg_ctrl: &'static DumpArgs,
    ) -> Self {
        Self {
            tcx,
            base_memo: Default::default(),
            inline_memo: Default::default(),
            ana_ctrl,
            dbg_ctrl,
            marker_carrying: InlineJudge::new(marker_ctx, tcx, ana_ctrl),
        }
    }

    pub fn is_clone_fn(&self, def_id: DefId) -> bool {
        self.tcx.trait_of_item(def_id) == self.tcx.lang_items().clone_trait()
    }

    /// How many (unique) functions we have analyzed
    pub fn cache_size(&self) -> usize {
        self.inline_memo.size()
    }

    /// Compute a procedure graph for this `body_id` (memoized). Actual
    /// computation performed by [`regal::compute_from_body_id`] and
    /// [`ProcedureGraph::from`]
    ///
    /// Returns `None` if we failed to get a function body for `def_id` (usually
    /// caused by trait objects).
    fn get_procedure_graph<'a>(
        &'a self,
        def_id: DefId,
    ) -> Option<&regal::Body<'tcx, DisplayViaDebug<Location>>> {
        self.base_memo
            .get(def_id, |_| {
                regal::compute_from_def_id(self.dbg_ctrl, def_id, self.tcx, &self.marker_carrying)
            })
            .as_ref()
    }

    /// Compute an inlined graph for this `body_id` (memoized)
    ///
    /// Returns `None` if wither we failed to get a function body for `def_id`
    /// (usually caused by trait objects) *or* this is a recursive request for
    /// the inlined graph of `def_id`.
    fn get_inlined_graph(&self, instance: FnResolution<'tcx>) -> Option<&InlinedGraph<'tcx>> {
        self.inline_memo
            .get(instance, |_| self.inline_graph(instance))?
            .as_ref()
    }

    /// Make the set of equations relative to the call site described by `gli`
    fn relativize_eqs<'a>(
        &'a self,
        equations: &'a Equations<GlobalLocal<'tcx>>,
        here: GlobalLocationS,
    ) -> impl Iterator<Item = Equation<GlobalLocal<'tcx>>> + 'a {
        equations
            .iter()
            .map(move |eq| eq.map_bases(move |base| base.add_location_frame(here)))
    }

    /// Get the `regal` call description for the call site at a specific
    /// location.
    ///
    /// # Panics
    ///
    /// When we cannot get a function body for `loc.innermost_function()`. This
    /// is considered ICE as no `GlobalLocation` should (by construction) ever
    /// reference locations in functions where we don't have access to the body.
    fn get_call(
        &self,
        loc: GlobalLocation,
    ) -> &regal::Call<'tcx, regal::Dependencies<DisplayViaDebug<mir::Location>>> {
        let body = self
            .get_procedure_graph(loc.innermost_function())
            .unwrap_or_else(|| {
                panic!("Invariant broken: location {loc} points into unavailable body")
            });
        &body.calls[&DisplayViaDebug(loc.innermost_location())]
    }

    // /// Calculate the global local that corresponds to input index `idx` at this `node`.
    // ///
    // /// If the node is not a [`SimpleLocation::Call`], then the index is ignored.
    // fn node_to_local(
    //     &self,
    //     node: &StdNode<'tcx>,
    //     idx: ArgNum,
    //     context: FnResolution<'tcx>,
    // ) -> GlobalLocal<'tcx> {
    //     match node {
    //         SimpleLocation::Return => GlobalLocal::at_root(self.tcx, mir::RETURN_PLACE, context),
    //         SimpleLocation::Argument(idx) => GlobalLocal::at_root(self.tcx, (*idx).into(), context),
    //         SimpleLocation::Call((loc, did)) => {
    //             let call = self.get_call(*loc);
    //             let pure_local = call.arguments[(idx as usize).into()]
    //                 .as_ref()
    //                 .map(|i| i.0)
    //                 .unwrap();
    //             assert_eq!(context.def_id(), loc.outermost_function());
    //             if let Some(parent) = loc.parent() {
    //                 GlobalLocal::relative(self.tcx, pure_local, parent, *did)
    //             } else {
    //                 assert_eq!(context.def_id(), loc.innermost_function());
    //                 GlobalLocal::at_root(self.tcx, pure_local, context)
    //             }
    //         }
    //     }
    // }

    fn writeable_arguments<'tc>(
        fn_sig: &ty::FnSig<'tc>,
    ) -> impl Iterator<Item = regal::ArgumentIndex> + 'tc {
        fn_sig.inputs().iter().enumerate().filter_map(|(i, t)| {
            t.is_mutable_ptr()
                .then(|| regal::ArgumentIndex::from_usize(i))
        })
    }

    fn classify_special_function_handling(
        &self,
        function: FnResolution<'tcx>,
        id: StdNode<'tcx>,
        g: &GraphImpl<'tcx, GlobalLocation>,
    ) -> Option<DropAction> {
        if self.ana_ctrl.drop_poll()
            && let Some(wrap) = is_part_of_async_desugar(self.tcx, id, g) {
                Some(wrap.to_owned())
        } else if self.ana_ctrl.drop_clone() && self.is_clone_fn(function.def_id()) {
            Some(vec![algebra::Operator::RefOf])
        } else {
            None
        }
    }

    pub fn get_controller_graph(
        &self,
        instance: FnResolution<'tcx>,
    ) -> Option<&InlinedGraph<'tcx>> {
        let tcx = self.tcx;
        if !tcx.asyncness(instance.def_id()).is_async() {
            return self.get_inlined_graph(instance);
        }
        let body_with_facts = self.tcx.body_for_def_id(instance.def_id()).unwrap();
        let body = body_with_facts.simplified_body();
        // XXX This might become invalid if functions other than `async` can create generators
        let Some(closure_fn) =
            (*body.basic_blocks).iter().find_map(|bb| {
                let stmt = bb.statements.last()?;
                if let mir::StatementKind::Assign(assign) = &stmt.kind
                    && let mir::Rvalue::Aggregate(box mir::AggregateKind::Generator(gid, substs, _), _) = &assign.1 {
                    Some(FnResolution::Final(ty::Instance::expect_resolve(tcx, ty::ParamEnv::reveal_all(), *gid, substs)))
                } else {
                    None
                }
            })
        else {
            tcx.sess.span_err(
                tcx.def_span(instance.def_id()),
                "ICE: Found this function to be async but could not extract the generator."
            );
            return None;
        };
        self.get_inlined_graph(closure_fn)
    }

    // #[allow(dead_code)]
    // fn try_inline_as_async_fn(
    //     &self,
    //     i_graph: &mut InlinedGraph<'tcx>,
    //     instance: FnResolution<'tcx>,
    // ) -> bool {
    //     let tcx = self.tcx;
    //     if !tcx.asyncness(instance.def_id()).is_async() {
    //         return false;
    //     }
    //     let body_with_facts = self.tcx.body_for_def_id(instance.def_id()).unwrap();
    //     let body = body_with_facts.simplified_body();
    //     let num_args = body.args_iter().count();
    //     // XXX This might become invalid if functions other than `async` can create generators
    //     let Some(closure_fn) =
    //         (*body.basic_blocks).iter().find_map(|bb| {
    //             let stmt = bb.statements.last()?;
    //             if let mir::StatementKind::Assign(assign) = &stmt.kind
    //                 && let mir::Rvalue::Aggregate(box mir::AggregateKind::Generator(gid, substs, _), _) = &assign.1 {
    //                 Some(FnResolution::Final(ty::Instance::expect_resolve(tcx, ty::ParamEnv::reveal_all(), *gid, substs)))
    //             } else {
    //                 None
    //             }
    //         })
    //     else {
    //         tcx.sess.span_err(
    //             tcx.def_span(instance.def_id()),
    //             "ICE: Found this function to be async but could not extract the generator."
    //         );
    //         return false;
    //     };
    //     let standard_edge: Edge = std::iter::once(EdgeType::Data(0)).collect();
    //     let incoming = (0..num_args)
    //         .map(|a| (SimpleLocation::Argument(a.into()), standard_edge))
    //         .collect::<Vec<_>>();
    //     let outgoing = [(SimpleLocation::Return, standard_edge)];
    //     let return_location = match body
    //         .basic_blocks
    //         .iter_enumerated()
    //         .filter_map(|(bb, bbdat)| {
    //             matches!(bbdat.terminator().kind, mir::TerminatorKind::Return).then_some(bb)
    //         })
    //         .collect::<Vec<_>>()
    //         .as_slice()
    //     {
    //         [bb] => body.terminator_loc(*bb),
    //         _ => unreachable!(),
    //     };

    //     let root_location = GlobalLocation::single(return_location, instance.def_id());

    //     // Following we must simulate two code rewrites to the body of this
    //     // function to simulate calling the closure. We make the closure
    //     // argument a fresh variable and we break existing connections of
    //     // arguments and return. The latter will be restored by the inlining
    //     // routine.

    //     // We invent a new variable here that stores the closure. Rustc uses _0
    //     // (the return place) to store it but we will overwrite that with the
    //     // return of calling the closure. However that would connect the inputs
    //     // and outputs in the algebra *if* we did not invent this new temporary
    //     // for the closure.
    //     let new_closure_local = regal::get_highest_local(body) + 5000;

    //     for term in i_graph.equations.iter_mut().flat_map(|eq| eq.unsafe_refs()) {
    //         assert!(term.base.location().is_none());
    //         if term.base.local() == mir::RETURN_PLACE {
    //             term.base.local = new_closure_local;
    //         }
    //     }

    //     // Break the return connections
    //     //
    //     // Actually clears the graph, but that is fine, because whenever we
    //     // insert edges (as the inlining routine will do later) we
    //     // automatically create the source and target nodes if they don't exist.
    //     i_graph.graph.clear();

    //     debug!(
    //         "Recognized {} as an async function",
    //         self.tcx.def_path_debug_str(instance.def_id())
    //     );
    //     self.inline_one_function(
    //         i_graph,
    //         instance,
    //         closure_fn,
    //         &incoming,
    //         &outgoing,
    //         &[Some(new_closure_local), None],
    //         Some(mir::RETURN_PLACE),
    //         &mut HashSet::default(),
    //         root_location,
    //     );
    //     true
    // }

    #[allow(clippy::type_complexity)]
    #[allow(clippy::too_many_arguments)]
    fn inline_one_function(
        &self,
        InlinedGraph {
            graph: g,
            equations: eqs,
            num_inlined,
            max_call_stack_depth,
        }: &mut InlinedGraph<'tcx>,
        caller_function: FnResolution<'tcx>,
        inlining_target: FnResolution<'tcx>,
        incoming: &[(StdNode<'tcx>, Edge)],
        outgoing: &[(StdNode<'tcx>, Edge)],
        arguments: &[Option<mir::Local>],
        return_to: Option<mir::Local>,
        queue_for_pruning: &mut EdgeSet<'tcx>,
        root_location: GlobalLocation,
        span: Span,
    ) {
        let Some(grw_to_inline) = self.get_inlined_graph(inlining_target) else {
            // Breaking recursion. This can only happen if we are trying to
            // inline ourself, so we simply skip.
            return;
        };
        *num_inlined += 1 + grw_to_inline.inlined_functions_count();
        *max_call_stack_depth =
            (*max_call_stack_depth).max(grw_to_inline.max_call_stack_depth() + 1);
        let mut argument_map: HashMap<_, _> = arguments
            .iter()
            .enumerate()
            .map(|(a, _)| (EdgeType::Data(a as u32), vec![]))
            .chain([(EdgeType::Control, vec![])])
            .collect();

        for e in incoming {
            for arg_num in e.1.into_types_iter() {
                argument_map.get_mut(&arg_num).unwrap().push(e.0);
            }
        }

        let here = GlobalLocationS {
            function: caller_function.def_id(),
            location: root_location.outermost_location(),
        };

        eqs.extend(self.relativize_eqs(&grw_to_inline.equations, here));

        let local_base_term =
            |local| Term::new_base(GlobalLocal::at_root(self.tcx, local, caller_function));
        let remote_base_term = |local| {
            Term::new_base(GlobalLocal::relative(
                self.tcx,
                local,
                root_location,
                inlining_target,
            ))
        };

        let regularly_handled_arguments: Vec<Option<mir::Local>> =
            if self.tcx.def_kind(inlining_target.def_id())
                == crate::rustc_hir::def::DefKind::Generator
            {
                let (fst, rest) = arguments.split_first().expect("No first argument");
                let fst = fst.expect("Not local argument");
                // In the special case of an async closure we may have to adjust the
                // first argument and the return value because for some reason when
                // we resolve the generic `poll` for an `async` function it just
                // directly returns the closure. `poll` has the signature
                // `fn(Pin<&mut [async body ...]>, Context<'_>) -> Poll<R>` whereas
                // the closure has the signature `fn([async body ...], ResumeTy) ->
                // R`. I don't know why this is but it means that algebra wise we
                // need to unwrap the actual first param with `.0` and `*` and wrap
                // the return with a `Poll::Ready` and `.0`.
                eqs.extend(
                    std::iter::once(algebra::Equality::new(
                        self.tcx,
                        local_base_term(fst)
                            .add_member_of(FieldIdx::from(0_usize).into())
                            .add_deref_of(),
                        remote_base_term(1_usize.into()),
                    ))
                    .chain(return_to.into_iter().map(|local| {
                        algebra::Equality::new(
                            self.tcx,
                            local_base_term(local)
                                .add_downcast(None, 0)
                                .add_member_of(mir::Field::from(0_usize).into()),
                            remote_base_term(mir::RETURN_PLACE),
                        )
                    }))
                    .map(|r| {
                        r.unwrap_or_else(|err| {
                            self.tcx.sess.span_fatal(
                                span,
                                format!("Failed to create special async equations: {err}"),
                            )
                        })
                    }),
                );
                [None, None]
                    .into_iter()
                    .chain(rest.iter().copied())
                    .collect()
            } else {
                std::iter::once(return_to)
                    .chain(arguments.iter().copied())
                    .collect()
            };

        eqs.extend(
            regularly_handled_arguments
                .into_iter()
                .enumerate()
                .filter_map(|(a, actual_param)| Some(((actual_param)?, a.into())))
                .map(|(actual_param, formal_param)| {
                    algebra::Equality::new(
                        self.tcx,
                        local_base_term(actual_param),
                        remote_base_term(formal_param),
                    )
                    .unwrap_or_else(|err| {
                        self.tcx.sess.span_fatal(
                            span,
                            format!("Failed to create regular argument equations: {err}"),
                        )
                    })
                }),
        );

        let to_inline = &grw_to_inline.graph;

        let mut connect_to = |g: &mut GraphImpl<'tcx, _>,
                              source: SimpleLocation<(GlobalLocation, _)>,
                              target,
                              weight: Edge,
                              pruning_required| {
            let mut add_edge = |source, register_for_pruning| {
                debug!("Connecting {source} -> {target}");
                if register_for_pruning {
                    queue_for_pruning.insert((source, target));
                }
                add_weighted_edge(g, source, target, weight)
            };
            match source {
                Node::Call((loc, did)) => {
                    add_edge(Node::Call((here.relativize(loc), did)), pruning_required)
                }
                Node::Return => unreachable!(),
                Node::Argument(a) => {
                    for nidx in argument_map
                        .get(&EdgeType::Data(a.as_usize() as u32))
                        .unwrap_or_else(|| self.tcx.sess.span_fatal(span, format!("Could not find {a} in arguments\n  call: {inlining_target}\n  arguments: {arguments:?}")))
                        .iter()
                    {
                        add_edge(*nidx, true)
                    }
                }
            }
        };

        for old in to_inline.nodes() {
            let new = old.map_call(|(location, function)| (here.relativize(*location), *function));
            g.add_node(new);
            debug!(
                "Handling {old} (now {new}) {} incoming edges",
                to_inline.edges_directed(old, pg::Incoming).count()
            );
            for edge in to_inline.edges_directed(old, pg::Incoming) {
                debug!("See incoming edge {} ({})", edge.source(), edge.weight());
                match new {
                    Node::Call(_) => connect_to(g, edge.source(), new, *edge.weight(), false),
                    Node::Return | Node::Argument(_) => {
                        for (target, out) in outgoing {
                            connect_to(g, edge.source(), *target, *out, true);
                        }
                    }
                }
            }
        }
    }

    /// Inline crate-local, non-marked called functions and return a set of
    /// newly inserted edges that cross those function boundaries to be
    /// inspected for pruning.
    ///
    /// Note that the edges in the set are not guaranteed to exist in the graph.
    fn perform_subfunction_inlining(
        &self,
        proc_g: &regal::Body<DisplayViaDebug<Location>>,
        i_graph: &mut InlinedGraph<'tcx>,
        instance: FnResolution<'tcx>,
    ) -> EdgeSet<'tcx> {
        let def_id = instance.def_id();
        let caller_local_def_id = def_id.expect_local();
        let recursive_analysis_enabled = self.ana_ctrl.use_recursive_analysis();
        let mut queue_for_pruning = HashSet::new();
        // if recursive_analysis_enabled && self.try_inline_as_async_fn(i_graph, instance) {
        //     debug!("Detected self to be async fn, closure was inlined.");
        //     return queue_for_pruning;
        // };
        let caller_body = self
            .tcx
            .body_for_def_id_default_policy(def_id)
            .unwrap()
            .simplified_body();
        let local_decls = &caller_body.local_decls;
        let targets = i_graph
            .graph
            .node_references()
            .filter_map(|(id, _)| match id {
                Node::Call((loc, fun)) => Some((id, loc, fun)),
                _ => None,
            })
            .filter_map(|(id, location, function)| {
                if recursive_analysis_enabled {
                    let def_id = function.def_id();
                    if let Some(ac) = self.classify_special_function_handling(
                        function,
                        id,
                        &i_graph.graph,
                    ) {
                        return Some((id, location, InlineAction::Drop(ac)));
                    }
                    if def_id.is_local()
                        && self.marker_carrying.should_inline(function)
                    {
                        debug!("Inlining {function:?}");
                        return Some((id, location, InlineAction::SimpleInline(function)));
                    } else if self.marker_carrying.marker_ctx().has_transitive_reachable_markers(function) {
                        self.tcx.sess.struct_span_warn(
                            self.tcx.def_span(def_id),
                            "This function is not being inlined, but a marker is reachable from its inside.",
                        ).span_note(
                            (caller_local_def_id, location.innermost_location()).span(self.tcx),
                            "Called from here"
                        ).emit()
                    }
                }
                let local_as_global = |l| GlobalLocal::at_root(self.tcx, l, instance);
                let call = self.get_call(location);
                debug!("Abstracting {function:?}");
                let fn_sig = function.sig(self.tcx).unwrap();
                let writeables = Self::writeable_arguments(&fn_sig)
                    .filter_map(|idx| call.arguments[idx].as_ref().map(|i| i.0))
                    .chain(call.return_to.into_iter())
                    .map(local_as_global)
                    .collect::<Vec<_>>();
                let mk_term = algebra::Term::new_base;
                i_graph
                    .equations
                    .extend(writeables.iter().flat_map(|&write| {
                        call.argument_locals()
                            .map(local_as_global)
                            .filter(move |read| *read != write)
                            .map(move |read| {
                                algebra::Equality::new(self.tcx, mk_term(write).add_unknown(), mk_term(read))
                                    .unwrap_or_else(|err|
                                        unreachable!("{err}")
                                    )
                            })
                    }));
                None
            })
            .collect::<Vec<_>>();
        for (idx, root_location, action) in targets {
            match action {
                InlineAction::SimpleInline(did) => {
                    assert!(root_location.is_at_root());
                    let incoming = i_graph
                        .graph
                        .edges_directed(idx, pg::Incoming)
                        .map(|e| (e.source(), *e.weight()))
                        .collect::<Vec<_>>();
                    let outgoing = i_graph
                        .graph
                        .edges_directed(idx, pg::Outgoing)
                        .map(|e| (e.target(), *e.weight()))
                        .collect::<Vec<_>>();
                    let call = &proc_g.calls[&DisplayViaDebug(root_location.outermost_location())];
                    let arguments = call
                        .arguments
                        .iter()
                        .map(|a| a.as_ref().map(|a| a.0))
                        .collect::<Vec<_>>();

                    let terminator = caller_body
                        .stmt_at(root_location.innermost_location())
                        .either(|_| unreachable!(), std::convert::identity);
                    debug!(
                        "Inlining {:?} at {:?}\n  resolved to: {did}\n  incoming edges: {}\n  outgoing edges: {}",
                        terminator.kind,
                        terminator.source_info.span,
                        incoming.len(),
                        outgoing.len()
                    );
                    self.inline_one_function(
                        i_graph,
                        instance,
                        did,
                        &incoming,
                        &outgoing,
                        &arguments,
                        call.return_to,
                        &mut queue_for_pruning,
                        root_location,
                        terminator.source_info.span,
                    );
                }
                InlineAction::Drop(wraps) => {
                    let incoming_closure = i_graph
                        .graph
                        .edges_directed(idx, pg::Direction::Incoming)
                        .filter_map(|(from, _, weight)| {
                            weight.has_type(EdgeType::Data(0)).then_some(from)
                        })
                        .collect::<Vec<_>>();
                    let outgoing = i_graph
                        .graph
                        .edges_directed(idx, pg::Direction::Outgoing)
                        .filter_map(|(_, to, weight)| {
                            let mut weight = *weight;
                            weight.remove_type(EdgeType::Control);
                            (!weight.is_empty()).then_some((to, weight))
                        })
                        .collect::<Vec<_>>();

                    for from in incoming_closure {
                        for (to, weight) in outgoing.iter().cloned() {
                            queue_for_pruning.insert((from, to));
                            add_weighted_edge(&mut i_graph.graph, from, to, weight)
                        }
                    }
                    let call = self.get_call(root_location);
                    if let Some(return_local) = call.return_to {
                        let mut target = algebra::Term::new_base(GlobalLocal::at_root(
                            self.tcx,
                            return_local,
                            instance,
                        ));
                        let argument = call.arguments[regal::ArgumentIndex::from_usize(0)]
                            .as_ref()
                            .unwrap()
                            .0;
                        if let Err(e) = wrapping_sanity_check(
                            self.tcx,
                            mir::Place::from(return_local).ty(local_decls, self.tcx),
                            mir::Place::from(argument).ty(local_decls, self.tcx),
                            wraps.iter().copied(),
                        ) {
                            self.tcx.sess.span_fatal(
                                caller_body
                                    .stmt_at(root_location.innermost_location())
                                    .either(|s| s.source_info.span, |t| t.source_info.span),
                                e,
                            );
                        }
                        target = target.extend(wraps);
                        i_graph.equations.push(algebra::Equality::new(
                            self.tcx,
                            target,
                            algebra::Term::new_base(GlobalLocal::at_root(
                                self.tcx, argument, instance,
                            )),
                        ).unwrap_or_else(|err|
                            self.tcx.sess.span_fatal(
                                call.span,
                                format!("Failed creating equation for wrapped return of dropped function: {err}"),
                            )
                        ));
                    }
                }
            };
            i_graph.graph.remove_node(idx);
        }
        queue_for_pruning
    }

    /// In spite of the name of this function it not only inlines the graph but
    /// also first creates it (with [`Self::get_procedure_graph`]) and globalize
    /// it ([`to_global_graph`]).
    ///
    /// Returns `None` if we failed to retrieve a function body for this
    /// `def_id` (usually caused by trait objects)
    fn inline_graph(&self, instance: FnResolution<'tcx>) -> Option<InlinedGraph<'tcx>> {
        let def_id = instance.def_id();
        let local_def_id = def_id.expect_local();
        let proc_g = self.get_procedure_graph(def_id)?;
        let mut gwr = InlinedGraph::from_body(instance, proc_g, self.tcx);

        let name = body_name_pls(self.tcx, local_def_id).name;
        if self.dbg_ctrl.dump_pre_inline_graph() {
            dump_dot_graph(
                dump_file_pls(self.tcx, local_def_id, "pre-inline.gv").unwrap(),
                &gwr,
            )
            .unwrap();
        }
        if self.dbg_ctrl.dump_local_equations() {
            let mut eqout = dump_file_pls(self.tcx, local_def_id, "local.eqs").unwrap();
            for eq in &gwr.equations {
                use std::io::Write;
                writeln!(eqout, "{eq}").unwrap();
            }
        }

        let mut queue_for_pruning = time(&format!("Inlining subgraphs into '{name}'"), || {
            self.perform_subfunction_inlining(proc_g, &mut gwr, instance)
        });

        if self.ana_ctrl.remove_inconsequential_calls().is_enabled() {
            panic!("Removing inconsequential calls is no longer supported");
        }

        if self.dbg_ctrl.dump_global_equations() {
            let mut eqout = dump_file_pls(self.tcx, local_def_id, "global.eqs").unwrap();
            for eq in &gwr.equations {
                use std::io::Write;
                writeln!(eqout, "{eq}").unwrap();
            }
        }
        if self.dbg_ctrl.dump_inlined_graph() {
            dump_dot_graph(
                dump_file_pls(self.tcx, local_def_id, "inlined.gv").unwrap(),
                &gwr,
            )
            .unwrap();
        }
        if self.ana_ctrl.use_pruning() {
            let strategy = self.ana_ctrl.pruning_strategy();
            use crate::args::PruningStrategy;
            let edges_to_prune = if matches!(strategy, PruningStrategy::NotPreviouslyPrunedEdges) {
                Self::find_prunable_edges(&gwr)
            } else {
                if matches!(strategy, PruningStrategy::NewEdgesNotPreviouslyPruned) {
                    queue_for_pruning
                        .retain(|&(from, to)| !Self::edge_has_been_pruned_before(from, to));
                } else {
                    assert_eq!(strategy, PruningStrategy::NewEdges);
                }
                queue_for_pruning
            };
            self.prune_impossible_edges(&mut gwr, name, &edges_to_prune, instance);
            if self.dbg_ctrl.dump_inlined_pruned_graph() {
                dump_dot_graph(
                    dump_file_pls(self.tcx, local_def_id, "inlined-pruned.gv").unwrap(),
                    &gwr,
                )
                .unwrap();
            }
        }

        for eq in &gwr.equations {
            debug!("Checking {eq}");
            if let Err(e) = equation_sanity_check(self.tcx, eq) {
                let mut span: crate::rustc_error_messages::MultiSpan = self
                    .tcx
                    .def_ident_span(def_id)
                    .unwrap_or_else(|| self.tcx.def_span(def_id))
                    .into();
                span.push_span_label(eq.lhs().base().span(self.tcx, def_id), "left hand local");
                span.push_span_label(eq.rhs().base().span(self.tcx, def_id), "right hand local");
                self.tcx.sess.span_fatal(
                    span,
                    format!("Equation inconsistency during construction of PDG for: {e}"),
                );
            }
        }
        Some(gwr)
    }
}

impl<'tcx> GlobalLocal<'tcx> {
    fn span(self, tcx: TyCtxt<'tcx>, context: DefId) -> crate::rustc_span::Span {
        let body = tcx
            .body_for_def_id_default_policy(
                self.location().map_or(context, |l| l.innermost_function()),
            )
            .unwrap()
            .simplified_body();
        body.local_decls[self.local].source_info.span
    }
}

fn dump_dot_graph<W: std::io::Write>(mut w: W, g: &InlinedGraph) -> std::io::Result<()> {
    use petgraph::dot::*;
    write!(
        w,
        "{}",
        Dot::with_attr_getters(&g.graph, &[], &&|_, _| "".to_string(), &&|_, _| "shape=box"
            .to_string(),)
    )
}

impl<'tcx> Inliner<'tcx> {
    /// Turn the output of the inliner into the format the rest of the paralegal-flow pipeline
    /// understands.
    pub fn to_call_only_flow<A: FnMut(ArgNum) -> GlobalLocation>(
        &self,
        InlinedGraph { graph: g, .. }: &InlinedGraph<'tcx>,
        mut mk_arg: A,
    ) -> crate::ir::CallOnlyFlow {
        let mut location_dependencies = HashMap::new();
        let mut return_dependencies = HashSet::new();

        let mut get_dependencies = |n| {
            let mut input_deps = vec![];
            let mut ctrl_deps = HashSet::new();
            for e in g.edges_directed(n, pg::Incoming) {
                for w in e.weight().into_types_iter() {
                    let target = if let EdgeType::Data(a) = w {
                        let aidx = a as usize;
                        if aidx >= input_deps.len() {
                            input_deps.resize_with(aidx + 1, HashSet::new);
                        }
                        &mut input_deps[aidx]
                    } else {
                        &mut ctrl_deps
                    };

                    target.insert(match e.source() {
                        Node::Call(c) => c.0,
                        Node::Return => unreachable!(),
                        Node::Argument(a) => mk_arg(a.as_usize() as u32),
                    });
                }
            }
            crate::ir::CallDeps {
                input_deps,
                ctrl_deps,
            }
        };

        for (idx, n) in g.node_references() {
            match n {
                Node::Argument(_) => (),
                Node::Return => {
                    for d in get_dependencies(idx)
                        .input_deps
                        .iter()
                        .flat_map(HashSet::iter)
                    {
                        return_dependencies.insert(*d);
                    }
                }
                Node::Call((loc, _)) => assert!(location_dependencies
                    .insert(*loc, get_dependencies(idx))
                    .is_none()),
            }
        }

        CallOnlyFlow {
            location_dependencies,
            return_dependencies,
        }
    }
}

pub fn equation_sanity_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    eq: &Equation<GlobalLocal<'tcx>>,
) -> Result<(), String> {
    let mut eq = eq.clone();
    eq.rearrange_left_to_right();
    assert!(eq.lhs().terms_inside_out().is_empty());

    let (lhs, rhs) = eq.decompose();

    let wrap = rhs.terms_inside_out().iter().copied();

    wrapping_sanity_check(tcx, lhs.base.ty, rhs.base.ty, wrap)
}

pub fn wrapping_sanity_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut left: mir::tcx::PlaceTy<'tcx>,
    mut right: mir::tcx::PlaceTy<'tcx>,
    wrap: impl IntoIterator<Item = Operator<DisplayViaDebug<mir::Field>>>,
) -> Result<(), String> {
    use mir::tcx::PlaceTy;
    use mir::ProjectionElem::{self, *};
    use Operator::*;
    let wrap = wrap.into_iter().collect::<Vec<_>>();
    if wrap.iter().copied().any(Operator::is_unknown) {
        return Ok(());
    }
    let apply_deref = |target: &mut PlaceTy<'tcx>| *target = target.projection_ty(tcx, Deref);
    let apply_field = |target: &mut PlaceTy<'tcx>, idx: mir::Field| {
        *target = match target.ty.kind() {
            ty::TyKind::Closure(_did, sub) => {
                assert!(target.variant_index.is_none(), "{target:?}");
                PlaceTy {
                    ty: sub
                        .as_closure()
                        .upvar_tys()
                        .nth(idx.as_usize())
                        .unwrap_or_else(|| {
                            panic!("{target:?} does not have enough upvars for {idx:?}")
                        }),
                    variant_index: None,
                }
            }
            ty::TyKind::Generator(did, substs, _) => {
                // I'm guessing here as to how generators actually work. My
                // working theory is that there are a number of "prefix" fields
                // that are accessible without using a variant index, followed
                // by a number of "state types" which are only accessible after
                // downcasting to a specific variant. My assumption also is that
                // both those indices are 0-based.
                //
                // Unfortunately I can't think if a good way to be defensive
                // wrt. those assumptions.
                let generator = substs.as_generator();
                debug!(
                    "Prefix tys: {:?}, State tys: {:?}",
                    Vec::from_iter(generator.prefix_tys()),
                    generator
                        .state_tys(*did, tcx)
                        .map(Vec::from_iter)
                        .collect::<Vec<_>>()
                );
                let ty = if let Some(v) = target.variant_index {
                    generator
                        .state_tys(*did, tcx)
                        .nth(v.as_usize())
                        .expect("Not enough variants")
                        .nth(idx.as_usize())
                        .expect("Not enough types")
                } else {
                    generator.prefix_tys().nth(idx.as_usize()).unwrap()
                };
                PlaceTy {
                    ty,
                    variant_index: None,
                }
            }
            _ => PlaceTy {
                ty: target.field_ty(tcx, idx),
                variant_index: None,
            },
        }
    };
    let apply_index =
        |target: &mut PlaceTy<'tcx>| *target = target.projection_ty(tcx, Index(0_usize.into()));
    let apply_downcast = |target: &mut PlaceTy<'tcx>, v| {
        *target = target.projection_ty(tcx, mir::PlaceElem::Downcast(None, v))
    };

    // This is kind of complicated because the wrappings need to be applied in
    // opposite order to both of the two types. I think there's also an
    // invariant by which you only have "in" wrappings first followed by "out"
    // wrappings (meaning whether they need to apply to left or right).
    //
    // As such it is split into one closure that applies the wraps that need to
    // apply to the right type, then the one's that need to apply to the left
    // one.
    wrap.into_iter()
        .filter_map(|op| match op {
            DerefOf => {
                apply_deref(&mut right);
                None
            }
            RefOf => Some(Deref),
            MemberOf(f) => {
                apply_field(&mut right, f.0);
                None
            }
            ContainsAt(f) => Some(Field(*f, ())),
            IndexOf => {
                apply_index(&mut right);
                None
            }
            ArrayWith => Some(Index(())),
            Operator::Downcast(v) => {
                apply_downcast(&mut right, v.into());
                None
            }
            Operator::Upcast(v) => Some(ProjectionElem::Downcast(None, v.into())),
            Unknown => unreachable!(),
        })
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .for_each(|for_left| match for_left {
            Deref => apply_deref(&mut left),
            Field(f, _) => apply_field(&mut left, f),
            Index(_) => apply_index(&mut left),
            ProjectionElem::Downcast(_, v) => apply_downcast(&mut left, v),
            _ => unreachable!(),
        });
    if tcx.normalize_erasing_regions(
        ty::ParamEnv::reveal_all(),
        left.ty.is_similar_enough(
            &tcx.normalize_erasing_regions(ty::ParamEnv::reveal_all(), right.ty),
            tcx.lang_items(),
        ),
    ) && left.variant_index == right.variant_index
    {
        Ok(())
    } else {
        Err(format!(
            "Sanity check failed:\n     {left:?}\n  != {right:?}"
        ))
    }
}

trait APoorPersonsEquivalenceCheck {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool;
}

impl<T: APoorPersonsEquivalenceCheck> APoorPersonsEquivalenceCheck for ty::List<T> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .zip(other.iter())
                .all(|(left, right)| left.is_similar_enough(right, language_items))
    }
}

impl<'tcx> APoorPersonsEquivalenceCheck for ty::GenericArg<'tcx> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        use ty::GenericArgKind::*;
        match (self.unpack(), other.unpack()) {
            (Lifetime(_), Lifetime(_)) => true,
            (Type(t_a), Type(t_b)) => t_a.is_similar_enough(&t_b, language_items),
            (Const(c_1), Const(c_2)) => c_1.is_similar_enough(&c_2, language_items),
            _ => false,
        }
    }
}

impl<'tcx> APoorPersonsEquivalenceCheck for ty::Const<'tcx> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        self.kind() == other.kind() && self.ty().is_similar_enough(&other.ty(), language_items)
    }
}

impl<'tcx, T: APoorPersonsEquivalenceCheck> APoorPersonsEquivalenceCheck for ty::Binder<'tcx, T> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        self.bound_vars() == other.bound_vars()
            && self
                .as_ref()
                .skip_binder()
                .is_similar_enough(other.as_ref().skip_binder(), language_items)
    }
}

impl<'tcx> APoorPersonsEquivalenceCheck for ty::FnSig<'tcx> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        self.inputs_and_output
            .is_similar_enough(other.inputs_and_output, language_items)
            && self.c_variadic == other.c_variadic
            && self.unsafety == other.unsafety
            && self.abi == other.abi
    }
}

impl<'tcx> APoorPersonsEquivalenceCheck for ty::ExistentialPredicate<'tcx> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        use ty::ExistentialPredicate::*;
        use ty::TermKind::*;
        match (self, other) {
            (Trait(t_1), Trait(t_2)) => {
                t_1.def_id == t_2.def_id && t_1.substs.is_similar_enough(t_2.substs, language_items)
            }
            (Projection(p_1), Projection(p_2)) => {
                p_1.def_id == p_2.def_id
                    && p_1.substs.is_similar_enough(p_2.substs, language_items)
                    && match (p_1.term.unpack(), p_2.term.unpack()) {
                        (Ty(t_1), Ty(t_2)) => t_1.is_similar_enough(&t_2, language_items),
                        (Const(c_1), Const(c_2)) => c_1.is_similar_enough(&c_2, language_items),
                        _ => false,
                    }
            }
            (AutoTrait(t_1), AutoTrait(t_2)) => t_1 == t_2,
            _ => false,
        }
    }
}

impl<'tcx> APoorPersonsEquivalenceCheck for ty::AliasTy<'tcx> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        self.def_id == other.def_id && self.substs.is_similar_enough(other.substs, language_items)
    }
}

impl<'a, T: APoorPersonsEquivalenceCheck> APoorPersonsEquivalenceCheck for &'a T {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        (*self).is_similar_enough(*other, language_items)
    }
}

impl<'tcx> APoorPersonsEquivalenceCheck for ty::Ty<'tcx> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        use crate::rust::rustc_type_ir::sty::TyKind::*;

        match (self.kind(), other.kind()) {
            (Int(a_i), Int(b_i)) => a_i == b_i,
            (Uint(a_u), Uint(b_u)) => a_u == b_u,
            (Float(a_f), Float(b_f)) => a_f == b_f,
            (Adt(a_d, a_s), Adt(b_d, b_s)) => {
                a_d == b_d && a_s.is_similar_enough(b_s, language_items)
            }
            (Foreign(a_d), Foreign(b_d)) => a_d == b_d,
            // This is where it gets hacky, we will basically consider all arrays
            // and slices the same so long as the element type is the same,
            // regardless of length.
            //
            // In future this could be refined to properly consider subtyping
            // relations, but we don't know the "directionality" of the comparison
            // anyway so no point in trying right now.
            (Array(a_t, _) | Slice(a_t), Array(b_t, _) | Slice(b_t)) => {
                a_t.is_similar_enough(b_t, language_items)
            }
            (RawPtr(a_t), RawPtr(b_t)) => {
                a_t.mutbl == b_t.mutbl && a_t.ty.is_similar_enough(&b_t.ty, language_items)
            }
            // We will also ignore regions for now
            (Ref(_, a_t, a_m), Ref(_, b_t, b_m)) => {
                a_t.is_similar_enough(b_t, language_items) && a_m == b_m
            }
            (FnDef(a_d, a_s), FnDef(b_d, b_s)) => {
                a_d == b_d && a_s.is_similar_enough(b_s, language_items)
            }
            (FnPtr(a_s), FnPtr(b_s)) => a_s.is_similar_enough(b_s, language_items),
            // Ignoring regions again
            (Dynamic(a_p, _, a_repr), Dynamic(b_p, _, b_repr)) => {
                a_p.is_similar_enough(b_p, language_items) && a_repr == b_repr
            }
            (Closure(a_d, a_s), Closure(b_d, b_s)) => {
                a_d == b_d && a_s.is_similar_enough(b_s, language_items)
            }
            (Generator(a_d, a_s, a_m), Generator(b_d, b_s, b_m)) => {
                if a_d == b_d && a_s.is_similar_enough(b_s, language_items) && a_m == b_m {
                    true
                } else {
                    debug!("{a_d:?} {a_s:?} {a_m:?} != {b_d:?} {b_s:?} {b_m:?}");
                    false
                }
            }
            (GeneratorWitness(a_g), GeneratorWitness(b_g)) => {
                // for some reason `a_g.equiv(b_g)` doesn't resolve properly and
                // gives me a type error so I inlined its body instead.
                a_g.bound_vars() == b_g.bound_vars()
                    && a_g
                        .skip_binder()
                        .is_similar_enough(b_g.skip_binder(), language_items)
            }
            (GeneratorWitnessMIR(a_d, a_s), GeneratorWitnessMIR(b_d, b_s)) => {
                a_d == b_d && a_s.is_similar_enough(b_s, language_items)
            }
            (Tuple(a_t), Tuple(b_t)) => a_t.is_similar_enough(b_t, language_items),
            (Alias(a_i, a_p), Alias(b_i, b_p)) => {
                a_i == b_i && a_p.is_similar_enough(b_p, language_items)
            }
            //(Param(a_p), Param(b_p)) => a_p == b_p,

            // We try to substitute parameters but sometimes they stick around
            // and Justus is not sure why. So we just skip comparison if one is
            // a parameter
            (Param(_), _) | (_, Param(_)) => true,
            (Bound(a_d, a_b), Bound(b_d, b_b)) => a_d == b_d && a_b == b_b,
            (Placeholder(a_p), Placeholder(b_p)) => a_p == b_p,
            (Infer(a_t), Infer(b_t)) => a_t == b_t,
            (Error(a_e), Error(b_e)) => a_e == b_e,
            (Bool, Bool) | (Char, Char) | (Str, Str) | (Never, Never) => true,
            (Adt(a, _), Ref(_, b, Mutability::Mut)) | (Ref(_, b, Mutability::Mut), Adt(a, _))
                if Some(a.did()) == language_items.resume_ty() =>
            {
                matches!(b.kind(), Adt(c, _) if Some(c.did()) == language_items.context())
            }
            // This is created when certain async functions are called. We could
            // additionally check that the input and output types match but I'm
            // lazy atm.
            (Dynamic(bound_predicate, _, _), Generator(_, _, _))
            | (Generator(_, _, _), Dynamic(bound_predicate, _, _)) => {
                debug!("Testing {self:?} and {other:?}\n  {bound_predicate:?}");
                matches!(
                    bound_predicate.first(),
                    Some(predicate)
                    if matches!(
                        predicate.skip_binder(),
                        ty::ExistentialPredicate::Trait(trait_predicate)
                        if Some(trait_predicate.def_id) == language_items.future_trait()
                    )
                )
            }
            // This is created by the `vec` macro when it uses `ShallowInitBox`
            (RawPtr(t_and_mut), _) | (_, RawPtr(t_and_mut))
                if t_and_mut.mutbl.is_mut()
                    && t_and_mut.ty.kind() == &ty::TyKind::Uint(ty::UintTy::U8) =>
            {
                self.is_box() && self.boxed_ty().is_array()
                    || other.is_box() && other.boxed_ty().is_array()
            }
            _ => false,
        }
    }
}
