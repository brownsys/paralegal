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
    ana::algebra::{self, Term},
    ir::{
        flows::CallOnlyFlow,
        regal::{self, SimpleLocation},
        GlobalLocation, GlobalLocationS,
    },
    mir,
    mir::Location,
    rust::hir::def_id::{DefId, LocalDefId},
    rustc_target::abi::FieldIdx,
    ty,
    utils::{
        body_name_pls, dump_file_pls, time, write_sep, DisplayViaDebug, FnResolution, Print,
        RecursionBreakingCache, TyCtxtExt,
    },
    AnalysisCtrl, DumpArgs, Either, HashMap, HashSet, MarkerCtx, Symbol, TyCtxt,
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
        id: LocalDefId,
    ) {
        if edges_to_prune.is_empty() {
            return;
        }
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
                algebra::graph::Graph::new(equations, DisplayViaDebug(id.to_def_id()));
            if self.dbg_ctrl.dump_locals_graph() {
                let f = dump_file_pls(self.tcx, id, "locals-graph.gv").unwrap();
                locals_graph.dump(f, |_| false, |_| false);
            }

            for &(from, to) in edges_to_prune {
                if let Some(weight) = graph.edge_weight_mut(from, to) {
                    for idx in weight.into_iter_data() {
                        let to_target = self.node_to_local(&to, idx);
                        // This can be optimized (directly create function)
                        let targets = match from {
                            Node::Argument(a) => Either::Right(std::iter::once(
                                GlobalLocal::at_root((a.as_usize() + 1).into()),
                            )),
                            Node::Return => unreachable!(),
                            Node::Call((location, _did)) => Either::Left({
                                let call = self.get_call(location);
                                let parent = location.parent();
                                call.argument_locals()
                                    .chain(call.return_to.into_iter())
                                    .map(move |local| {
                                        if let Some(parent) = parent {
                                            GlobalLocal::relative(local, parent)
                                        } else {
                                            GlobalLocal::at_root(local)
                                        }
                                    })
                            }),
                        }
                        .collect::<HashSet<_>>();
                        debug!(
                            "Solving for {to_target} to {}",
                            Print(|f| {
                                f.write_char('{')?;
                                write_sep(f, ", ", &targets, std::fmt::Display::fmt)?;
                                f.write_char('}')
                            })
                        );
                        let is_reachable =
                            locals_graph.reachable(to_target, |to| targets.contains(&to));

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
}

type BodyCache<'tcx> = Cache<DefId, regal::Body<'tcx, DisplayViaDebug<Location>>>;

/// Essentially just a bunch of caches of analyses.
pub struct Inliner<'tcx> {
    /// Memoized graphs created from single-procedure analyses
    base_memo: BodyCache<'tcx>,
    /// Memoized graphs that have all their callees inlined. Unlike `base_memo`
    /// this has to be recursion breaking, since a function may call itself
    /// (possibly transitively).
    inline_memo: RecursionBreakingCache<DefId, InlinedGraph<'tcx>>,
    tcx: TyCtxt<'tcx>,
    ana_ctrl: &'static AnalysisCtrl,
    dbg_ctrl: &'static DumpArgs,
    marker_carrying: InlineJudge<'tcx>,
}

fn is_part_of_async_desugar<'tcx, L: Copy + Ord + std::hash::Hash + std::fmt::Display>(
    tcx: TyCtxt<'tcx>,
    node: Node<(L, FnResolution<'tcx>)>,
    graph: &GraphImpl<'tcx, L>,
) -> Option<Option<algebra::Operator<DisplayViaDebug<FieldIdx>>>> {
    let lang_items = tcx.lang_items();
    // We use `?` here because if any of these functions aren't defined we can
    // just abort.
    let mut seen = [
        (lang_items.get_context_fn()?, None, false),
        (
            lang_items
                .into_future_fn()
                .and_then(|f| tcx.trait_of_item(f))?,
            None,
            false,
        ),
        // I used to add a
        // algebra::Operator::MemberOf(mir::Field::from_usize(0).into())
        // here as well, but while that is technically correct in erms
        // of what this function does, the new encoding for `poll`
        // strips that away before calling the closure, so now I just
        // don't. Probably cleaner would be to change the wrapping for
        // `poll` but I'm lazy
        (
            lang_items.new_unchecked_fn()?,
            Some(algebra::Operator::RefOf),
            false,
        ),
    ];
    let mut poll_fn_seen = false;
    let poll_fn_wrap = Some(algebra::Operator::Downcast(0));
    let mut queue = vec![node];
    let mut iterations = 0;
    let mut wrap_needed = None;

    // This complex abomination does a few things at once. Starting from the
    // given node it explores the neigbors in turn to see if, fanning out, we
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
    // since we match on the entire pattern only a function that is surrpounded
    // by all other async-desugaring operators would ever be considered
    // appropriate here so it is very unlikely to trigger for any non-async
    // desugared closure. Perhaps important to mentionhere too is that in the
    // pattern we look for the closure is in the middle of the other nodes. So
    // if by chance a closure in the periphery of such a pattern started to
    // match, the search over the pattern sould be abandoned and `None` returned
    // as soon as the "actual" `poll` style closure is encountered (because the
    // `poll` style function would already be marked as seen).

    while let Some(node) = queue.pop() {
        iterations += 1;
        if let SimpleLocation::Call((_, inst)) = node
            && let maybe_resolved_trait = tcx.impl_of_method(inst.def_id()).and_then(|impl_| tcx.trait_id_of_impl(impl_))
            && let Some((wrap, was_seen)) = seen.iter_mut().find(|(k, _, _)| *k == inst.def_id() || Some(*k) == maybe_resolved_trait).map(|(_, w, t)| (&*w, t))
                .or_else(|| {
                    tcx.is_closure(inst.def_id()).then_some((&poll_fn_wrap, &mut poll_fn_seen))
                })
            && !*was_seen
        {
            wrap_needed.get_or_insert(*wrap);
            *was_seen = true;
            queue.extend(graph.neighbors_directed(node, petgraph::Direction::Incoming));
            queue.extend(graph.neighbors_directed(node, petgraph::Direction::Outgoing))
        } else if iterations > 0 {
            debug!("{node} did not belong to pattern");
        }
    }
    if poll_fn_seen || seen.iter().any(|v| v.2) {
        debug!("Saw some async desugar pattern around node {node} in {iterations} iterations: \n   poll: {poll_fn_seen} {}", Print(|f| write_sep(f, "", seen, |elem, f| write!(f, "\n   {:?}: {}", elem.0, elem.2))))
    }
    (poll_fn_seen && seen.iter().all(|v| v.2))
        .then_some(wrap_needed)
        .flatten()
}

enum InlineAction {
    SimpleInline(LocalDefId),
    Drop(DropAction),
}

enum DropAction {
    None,
    WrapReturn(Vec<algebra::Operator<DisplayViaDebug<mir::Field>>>),
}

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
    fn get_procedure_graph<'a>(
        &'a self,
        def_id: DefId,
    ) -> &regal::Body<'tcx, DisplayViaDebug<Location>> {
        self.base_memo.get(def_id, |_| {
            regal::compute_from_def_id(self.dbg_ctrl, def_id, self.tcx, &self.marker_carrying)
        })
    }

    /// Compute an inlined graph for this `body_id` (memoized)
    pub fn get_inlined_graph(&self, def_id: DefId) -> Option<&InlinedGraph<'tcx>> {
        self.inline_memo.get(def_id, |bid| self.inline_graph(bid))
    }

    /// Convenience wrapper around [`Self::get_inlined_graph`]
    fn get_inlined_graph_by_def_id(&self, def_id: LocalDefId) -> Option<&InlinedGraph<'tcx>> {
        let _hir = self.tcx.hir();
        self.get_inlined_graph(def_id.to_def_id())
    }

    /// Make the set of equations relative to the call site described by `gli`
    fn relativize_eqs(
        equations: &Equations<GlobalLocal>,
        here: GlobalLocationS,
    ) -> impl Iterator<Item = Equation<GlobalLocal>> + '_ {
        equations.iter().map(move |eq| {
            eq.map_bases(|base| {
                GlobalLocal::relative(
                    base.local(),
                    base.location().map_or_else(
                        || GlobalLocation::single(here.location, here.function),
                        |prior| here.relativize(prior),
                    ),
                )
            })
        })
    }

    /// Get the `regal` call description for the call site at a specific location.
    fn get_call(
        &self,
        loc: GlobalLocation,
    ) -> &regal::Call<'tcx, regal::Dependencies<DisplayViaDebug<mir::Location>>> {
        let body = self.get_procedure_graph(loc.innermost_function());
        &body.calls[&DisplayViaDebug(loc.innermost_location())]
    }

    /// Calculate the global local that corresponds to input index `idx` at this `node`.
    ///
    /// If the node is not a [`SimpleLocation::Call`], then the index is ignored.
    fn node_to_local(&self, node: &StdNode<'tcx>, idx: ArgNum) -> GlobalLocal {
        match node {
            SimpleLocation::Return => GlobalLocal::at_root(mir::RETURN_PLACE),
            SimpleLocation::Argument(idx) => GlobalLocal::at_root((*idx).into()),
            SimpleLocation::Call((loc, _)) => {
                let call = self.get_call(*loc);
                let pure_local = call.arguments[(idx as usize).into()]
                    .as_ref()
                    .map(|i| i.0)
                    .unwrap();
                if let Some(parent) = loc.parent() {
                    GlobalLocal::relative(pure_local, parent)
                } else {
                    GlobalLocal::at_root(pure_local)
                }
            }
        }
    }

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
        function: DefId,
        id: StdNode<'tcx>,
        g: &GraphImpl<'tcx, GlobalLocation>,
    ) -> Option<DropAction> {
        if self.ana_ctrl.drop_poll()
            && let Some(maybe_wrap) = is_part_of_async_desugar(self.tcx, id, g) {
                Some(if let Some(wrap) = maybe_wrap {
                    DropAction::WrapReturn(vec![wrap])
                } else {
                    DropAction::None
                })
        } else if self.ana_ctrl.drop_clone() && self.is_clone_fn(function) {
            Some(DropAction::WrapReturn(vec![algebra::Operator::RefOf]))
        } else {
            None
        }
    }

    fn try_inline_as_async_fn(&self, i_graph: &mut InlinedGraph<'tcx>, def_id: DefId) -> bool {
        let body_with_facts = self.tcx.body_for_def_id(def_id).unwrap();
        let body = body_with_facts.simplified_body();
        let num_args = body.args_iter().count();
        // XXX This might become invalid if functions other than `async` can create generators
        let closure_fn =
            if let Some(bb) = (*body.basic_blocks).iter().last()
                && let Some(stmt) = bb.statements.last()
                && let mir::StatementKind::Assign(assign) = &stmt.kind
                && let mir::Rvalue::Aggregate(box mir::AggregateKind::Generator(gid, ..), _) = &assign.1 {

            *gid
        } else {
            return false;
        };
        let standard_edge: Edge = std::iter::once(EdgeType::Data(0)).collect();
        let incoming = (0..num_args)
            .map(|a| (SimpleLocation::Argument(a.into()), standard_edge))
            .collect::<Vec<_>>();
        let outgoing = [(SimpleLocation::Return, standard_edge)];
        let return_location = match body
            .basic_blocks
            .iter_enumerated()
            .filter_map(|(bb, bbdat)| {
                matches!(bbdat.terminator().kind, mir::TerminatorKind::Return).then_some(bb)
            })
            .collect::<Vec<_>>()
            .as_slice()
        {
            [bb] => body.terminator_loc(*bb),
            _ => unreachable!(),
        };

        let root_location = GlobalLocation::single(return_location, def_id);

        // Following we must sumilate two code rewrites to the body of this
        // function to simulate calling the closure. We make the closure
        // argument a fresh variable and we break existing connections of
        // arguments and return. The latter will be restored by the inlining
        // routine.

        // We invent a new variable here that stores the closure. Rustc uses _0
        // (the return place) to store it but we will overwrite that with the
        // return of calling the closure. However that would connect the inputs
        // and outputs in the algebra *if* we did not invent this new temporary
        // for the closure.
        let new_closure_local = regal::get_highest_local(body) + 1;

        for term in i_graph
            .equations
            .iter_mut()
            .flat_map(|eq| [&mut eq.rhs, &mut eq.lhs])
        {
            assert!(term.base.location().is_none());
            if term.base.local() == mir::RETURN_PLACE {
                term.base.local = new_closure_local;
            }
        }

        // Break the return connections
        //
        // Actuall clears the graph, but that is fine, because whenever we
        // insert endges (as the inlining routine will do later) we
        // automatically create the source and target nodes if they don't exist.
        i_graph.graph.clear();

        debug!(
            "Recognized {} as an async function",
            self.tcx.def_path_debug_str(def_id)
        );
        self.inline_one_function(
            i_graph,
            def_id,
            closure_fn.expect_local(),
            &incoming,
            &outgoing,
            &[Some(new_closure_local), None],
            Some(mir::RETURN_PLACE),
            &mut HashSet::default(),
            root_location,
        );
        true
    }

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
        caller_function: DefId,
        inlining_target: LocalDefId,
        incoming: &[(StdNode<'tcx>, Edge)],
        outgoing: &[(StdNode<'tcx>, Edge)],
        arguments: &[Option<mir::Local>],
        return_to: Option<mir::Local>,
        queue_for_pruning: &mut EdgeSet<'tcx>,
        root_location: GlobalLocation,
    ) {
        let grw_to_inline =
            if let Some(callee_graph) = self.get_inlined_graph_by_def_id(inlining_target) {
                callee_graph
            } else {
                // Breaking recursion. This can only happen if we are trying to
                // inline ourself, so we simply skip.
                return;
            };
        debug!(
            "Inlining {} with {} arguments and {} targets",
            self.tcx.def_path_debug_str(inlining_target.to_def_id()),
            incoming.len(),
            outgoing.len()
        );
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
            function: caller_function,
            location: root_location.outermost_location(),
        };
        eqs.extend(
            Self::relativize_eqs(&grw_to_inline.equations, here).chain(
                arguments
                    .iter()
                    .enumerate()
                    .filter_map(|(a, actual_param)| Some(((*actual_param)?, (a + 1).into())))
                    .chain(return_to.into_iter().map(|r| (r, mir::RETURN_PLACE)))
                    .map(|(actual_param, formal_param)| {
                        algebra::Equality::new(
                            Term::new_base(GlobalLocal::at_root(actual_param)),
                            Term::new_base(GlobalLocal::relative(formal_param, root_location)),
                        )
                    }),
            ),
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
                        .unwrap_or_else(|| panic!("Could not find {a} in arguments"))
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
        def_id: DefId,
    ) -> EdgeSet<'tcx> {
        let recursive_analysis_enabled = self.ana_ctrl.use_recursive_analysis();
        let mut queue_for_pruning = HashSet::new();
        if recursive_analysis_enabled && self.try_inline_as_async_fn(i_graph, def_id) {
            return queue_for_pruning;
        };
        let targets = i_graph
            .graph
            .node_references()
            .filter_map(|(id, n)| match n {
                Node::Call((loc, fun)) => Some((id, loc, fun)),
                _ => None,
            })
            .filter_map(|(id, location, function)| {
                if recursive_analysis_enabled {
                    debug!("Recursive analysis enabled");
                    if let Some(ac) = self.classify_special_function_handling(
                        function.def_id(),
                        id,
                        &i_graph.graph,
                    ) {
                        return Some((id, *location, InlineAction::Drop(ac)));
                    }
                    if let Some(local_id) = function.def_id().as_local()
                        && self.marker_carrying.should_inline(*function)
                    {
                        debug!("Inlining {function:?}");
                        return Some((id, *location, InlineAction::SimpleInline(local_id)));
                    }
                }
                let local_as_global = GlobalLocal::at_root;
                let call = self.get_call(*location);
                debug!("Abstracting {function:?}");
                let fn_sig = function.sig(self.tcx).skip_binder();
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
                                algebra::Equality::new(mk_term(write).add_unknown(), mk_term(read))
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
                    self.inline_one_function(
                        i_graph,
                        def_id,
                        did,
                        &incoming,
                        &outgoing,
                        &arguments,
                        call.return_to,
                        &mut queue_for_pruning,
                        root_location,
                    );
                }
                InlineAction::Drop(drop_action) => {
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
                        let mut target =
                            algebra::Term::new_base(GlobalLocal::at_root(return_local));
                        if let DropAction::WrapReturn(wrappings) = drop_action {
                            target = target.extend(wrappings);
                        }
                        i_graph.equations.push(algebra::Equality::new(
                            target,
                            algebra::Term::new_base(GlobalLocal::at_root(
                                call.arguments[regal::ArgumentIndex::from_usize(0)]
                                    .as_ref()
                                    .unwrap()
                                    .0,
                            )),
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
    fn inline_graph(&self, def_id: DefId) -> InlinedGraph<'tcx> {
        let local_def_id = def_id.expect_local();
        let proc_g = self.get_procedure_graph(def_id);
        let mut gwr = InlinedGraph::from_body(def_id, proc_g, self.tcx);

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
            self.perform_subfunction_inlining(proc_g, &mut gwr, def_id)
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
            self.prune_impossible_edges(&mut gwr, name, &edges_to_prune, local_def_id);
            if self.dbg_ctrl.dump_inlined_pruned_graph() {
                dump_dot_graph(
                    dump_file_pls(self.tcx, local_def_id, "inlined-pruned.gv").unwrap(),
                    &gwr,
                )
                .unwrap();
            }
        }
        gwr
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
