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
    hir::{self, BodyId},
    ir::{
        flows::CallOnlyFlow,
        global_location::IsGlobalLocation,
        regal::{self, SimpleLocation},
        GliAt, GlobalLocation, GLI,
    },
    mir,
    mir::Location,
    rust::hir::def_id::{DefId, LocalDefId},
    ty,
    utils::{
        body_name_pls, dump_file_pls, time, write_sep, DisplayViaDebug, IntoDefId, IntoLocalDefId,
        Print, RecursionBreakingCache,
    },
    AnalysisCtrl, DbgArgs, Either, HashMap, HashSet, MarkerCtx, Symbol, TyCtxt,
};

use rustc_utils::{cache::Cache, mir::borrowck_facts};

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

/// This essentially describes a closure that determines for a given
/// [`LocalDefId`] if it should be inlined. Originally this was in fact done by
/// passing a closure, but it couldn't properly satisfy the type checker,
/// because the selector has to be stored in `fluid_let` variable, which is a
/// dynamically scoped variable. This means that the type needs to be valid for
/// a static lifetime, which I believe closures are not.
///
/// In particular the way that this works is that values of this interface are
/// then wrapped with [`RecurseSelector`], which is a flowistry interface that
/// satisfies [`flowistry::extensions::RecurseSelector`]. The wrapper then
/// simply dispatches to the [`InlineSelector`].
///
/// The reason for the two tiers of selectors is that
///
/// - Flowistry is a separate crate and so I wanted a way to control it that
///   decouples from the specifics of dfpp
/// - We use the selectors to skip functions with annotations, but I wanted to
///   keep the construction of inlined flow graphs agnostic to any notion of
///   annotations. Those are handled by the [`CollectingVisitor`]
///
/// The only implementation currently in use for this is
/// [`SkipAnnotatedFunctionSelector`].
pub trait Oracle {
    fn should_inline(&self, did: LocalDefId) -> bool;
    fn is_semantically_meaningful(&self, did: DefId) -> bool;
    fn carries_marker(&self, did: DefId) -> bool;
}

impl<T: Oracle> Oracle for std::rc::Rc<T> {
    fn should_inline(&self, did: LocalDefId) -> bool {
        self.as_ref().should_inline(did)
    }
    fn is_semantically_meaningful(&self, did: DefId) -> bool {
        self.as_ref().is_semantically_meaningful(did)
    }
    fn carries_marker(&self, did: DefId) -> bool {
        self.as_ref().carries_marker(did)
    }
}

type EdgeSet<'g> = HashSet<(
    Node<(GlobalLocation<'g>, DefId)>,
    Node<(GlobalLocation<'g>, DefId)>,
)>;

impl<'tcx, 'g> Inliner<'tcx, 'g> {
    fn edge_has_been_pruned_before(
        from: Node<(GlobalLocation<'g>, DefId)>,
        to: Node<(GlobalLocation<'g>, DefId)>,
    ) -> bool {
        match (to, from) {
            (SimpleLocation::Call(c1), SimpleLocation::Call(c2)) => {
                c1.0.outermost() == c2.0.outermost()
            }
            (SimpleLocation::Call(c), _) | (_, SimpleLocation::Call(c)) => c.0.is_at_root(),
            _ => true,
        }
    }

    fn find_prunable_edges(graph: &InlinedGraph<'g>) -> EdgeSet<'g> {
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
        graph: &mut InlinedGraph<'g>,
        name: Symbol,
        edges_to_prune: &EdgeSet<'g>,
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

            let locals_graph = algebra::graph::new(equations);
            if self.dbg_ctrl.dump_locals_graph() {
                let f = dump_file_pls(self.tcx, id, "locals-graph.gv").unwrap();
                algebra::graph::dump(f, &locals_graph, |_| false, |_| false);
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
                                let parent = location.parent(self.gli);
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
                        let is_reachable = algebra::graph::reachable(
                            to_target,
                            |to| targets.contains(&to),
                            &locals_graph,
                        );

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

impl<'g> InlinedGraph<'g> {
    fn from_body(
        gli: GLI<'g>,
        body_id: BodyId,
        body: &regal::Body<DisplayViaDebug<Location>>,
        tcx: TyCtxt,
    ) -> Self {
        time("Graph Construction From Regal Body", || {
            let equations = to_global_equations(&body.equations, body_id, gli);
            let mut gwr = InlinedGraph {
                equations,
                graph: Default::default(),
                num_inlined: 0,
                max_call_stack_depth: 0,
            };
            let g = &mut gwr.graph;
            let call_map = body
                .calls
                .iter()
                .map(|(loc, call)| (loc, call.function))
                .collect::<HashMap<_, _>>();
            let return_node = g.add_node(Node::Return);

            let mut add_dep_edges =
                |to, idx, deps: &HashSet<regal::Target<DisplayViaDebug<Location>>>| {
                    for d in deps {
                        use regal::Target;
                        let from = match d {
                            Target::Call(c) => regal::SimpleLocation::Call((
                                gli.globalize_location(**c, body_id),
                                *call_map.get(c).unwrap_or_else(|| {
                                    panic!(
                                        "Expected to find call at {c} in function {}",
                                        tcx.def_path_debug_str(body_id.into_def_id(tcx))
                                    )
                                }),
                            )),
                            Target::Argument(a) => regal::SimpleLocation::Argument(*a),
                        };
                        if g.contains_edge(from, to) {
                            g[(from, to)].add_type(idx)
                        } else {
                            let mut edge = Edge::empty();
                            edge.add_type(idx);
                            g.add_edge(from, to, edge);
                        }
                    }
                };

            for (&loc, call) in body.calls.iter() {
                let n =
                    SimpleLocation::Call((gli.globalize_location(*loc, body_id), call.function));
                for (idx, deps) in call.arguments.iter().enumerate() {
                    if let Some((_, deps)) = deps {
                        add_dep_edges(n, EdgeType::Data(idx as u32), deps)
                    }
                }
                add_dep_edges(n, EdgeType::Control, &call.ctrl_deps);
            }
            add_dep_edges(return_node, EdgeType::Data(0_u32), &body.return_deps);
            for (idx, deps) in body.return_arg_deps.iter().enumerate() {
                add_dep_edges(
                    SimpleLocation::Argument(idx.into()),
                    EdgeType::Data(0_u32),
                    deps,
                );
            }

            gwr
        })
    }
}

type BodyCache = Cache<BodyId, regal::Body<DisplayViaDebug<Location>>>;

/// Essentially just a bunch of caches of analyses.
pub struct Inliner<'tcx, 'g> {
    /// Memoized graphs created from single-procedure analyses
    base_memo: BodyCache,
    /// Memoized graphs that have all their callees inlined. Unlike `base_memo`
    /// this has to be recursion breaking, since a function may call itself
    /// (possibly transitively).
    inline_memo: RecursionBreakingCache<BodyId, InlinedGraph<'g>>,
    tcx: TyCtxt<'tcx>,
    gli: GLI<'g>,
    ana_ctrl: &'static AnalysisCtrl,
    dbg_ctrl: &'static DbgArgs,
    marker_carrying: InlineJudge<'tcx>,
}

/// Globalize all locations mentioned in these equations.
fn to_global_equations<'g>(
    eqs: &Equations<DisplayViaDebug<mir::Local>>,
    _body_id: BodyId,
    _gli: GLI<'g>,
) -> Equations<GlobalLocal<'g>> {
    eqs.iter()
        .map(|eq| eq.map_bases(|target| GlobalLocal::at_root(**target)))
        .collect()
}

fn is_part_of_async_desugar<L: Copy + Ord + std::hash::Hash>(
    lang_items: &hir::LanguageItems,
    node: Node<(L, DefId)>,
    graph: &GraphImpl<L>,
) -> bool {
    let mut seen = [
        (lang_items.future_poll_fn(), false),
        (lang_items.get_context_fn(), false),
        (lang_items.into_future_fn(), false),
        (lang_items.new_unchecked_fn(), false),
    ];
    let mut queue = vec![node];
    while let Some(node) = queue.pop() {
        if let SimpleLocation::Call((_, def_id)) = node {
            if let Some((_, was_seen)) = seen.iter_mut().find(|(k, _)| *k == Some(def_id)) {
                if *was_seen {
                    continue;
                }
                *was_seen = true;
                queue.extend(graph.neighbors_directed(node, petgraph::Direction::Incoming));
                queue.extend(graph.neighbors_directed(node, petgraph::Direction::Outgoing))
            }
        }
    }
    seen.iter().all(|v| v.1)
}

enum InlineAction {
    SimpleInline(LocalDefId),
    Drop(DropAction),
}

enum DropAction {
    None,
    WrapReturn(Vec<algebra::Operator<DisplayViaDebug<mir::Field>>>),
}

impl<'tcx, 'g> Inliner<'tcx, 'g> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        gli: GLI<'g>,
        marker_ctx: MarkerCtx<'tcx>,
        ana_ctrl: &'static AnalysisCtrl,
        dbg_ctrl: &'static DbgArgs,
    ) -> Self {
        Self {
            tcx,
            gli,
            base_memo: Default::default(),
            inline_memo: Default::default(),
            ana_ctrl,
            dbg_ctrl,
            marker_carrying: InlineJudge::new(marker_ctx, tcx),
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
        body_id: BodyId,
    ) -> &regal::Body<DisplayViaDebug<Location>> {
        self.base_memo.get(body_id, |bid| {
            regal::compute_from_body_id(
                self.dbg_ctrl,
                bid,
                self.tcx,
                self.gli,
                &self.marker_carrying,
                self.ana_ctrl,
            )
        })
    }

    /// Compute an inlined graph for this `body_id` (memoized)
    pub fn get_inlined_graph(&self, body_id: BodyId) -> Option<&InlinedGraph<'g>> {
        self.inline_memo.get(body_id, |bid| self.inline_graph(bid))
    }

    /// Convenience wrapper around [`Self::get_inlined_graph`]
    fn get_inlined_graph_by_def_id(&self, def_id: LocalDefId) -> Option<&InlinedGraph<'g>> {
        let hir = self.tcx.hir();
        let body_id = match hir.maybe_body_owned_by(def_id) {
            None => {
                warn!(
                    "no body id for {:?}",
                    self.tcx.def_path_debug_str(def_id.into_def_id(self.tcx))
                );
                return None;
            }
            Some(b) => b,
        };
        self.get_inlined_graph(body_id)
    }

    /// Make the set of equations relative to the call site described by `gli`
    fn relativize_eqs<'a>(
        equations: &'a Equations<GlobalLocal<'g>>,
        gli: &'a GliAt<'g>,
    ) -> impl Iterator<Item = Equation<GlobalLocal<'g>>> + 'a {
        equations.iter().map(move |eq| {
            eq.map_bases(|base| {
                GlobalLocal::relative(
                    base.local(),
                    base.location()
                        .map_or_else(|| gli.as_global_location(), |prior| gli.relativize(prior)),
                )
            })
        })
    }

    /// Get the `regal` call description for the call site at a specific location.
    fn get_call(
        &self,
        loc: GlobalLocation<'g>,
    ) -> &regal::Call<regal::Dependencies<DisplayViaDebug<mir::Location>>> {
        let body = self.get_procedure_graph(loc.innermost_function());
        &body.calls[&DisplayViaDebug(loc.innermost_location())]
    }

    /// Calculate the global local that corresponds to input index `idx` at this `node`.
    ///
    /// If the node is not a [`SimpleLocation::Call`], then the index is ignored.
    fn node_to_local(
        &self,
        node: &Node<(GlobalLocation<'g>, DefId)>,
        idx: ArgNum,
    ) -> GlobalLocal<'g> {
        match node {
            SimpleLocation::Return => GlobalLocal::at_root(mir::RETURN_PLACE),
            SimpleLocation::Argument(idx) => GlobalLocal::at_root((*idx).into()),
            SimpleLocation::Call((loc, _)) => {
                let call = self.get_call(*loc);
                let pure_local = call.arguments[(idx as usize).into()]
                    .as_ref()
                    .map(|i| i.0)
                    .unwrap();
                if let Some(parent) = loc.parent(self.gli) {
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
        id: Node<(GlobalLocation<'g>, DefId)>,
        g: &GraphImpl<GlobalLocation<'g>>,
    ) -> Option<DropAction> {
        let language_items = self.tcx.lang_items();
        if self.ana_ctrl.drop_poll() && is_part_of_async_desugar(language_items, id, g) {
            Some(if Some(function) == language_items.new_unchecked_fn() {
                // I used to add a
                // algebra::Operator::MemberOf(mir::Field::from_usize(0).into())
                // here as well, but while that is technically correct in erms
                // of what this function does, the new encoding for `poll`
                // strips that away before calling the closure, so now I just
                // don't. Probably cleaner would be to change the wrapping for
                // `poll` but I'm lazy
                DropAction::WrapReturn(vec![algebra::Operator::RefOf])
            } else if Some(function) == language_items.future_poll_fn() {
                DropAction::WrapReturn(vec![algebra::Operator::Downcast(0)])
            } else {
                DropAction::None
            })
        } else if self.ana_ctrl.drop_clone() && self.is_clone_fn(function) {
            Some(DropAction::WrapReturn(vec![algebra::Operator::RefOf]))
        } else {
            None
        }
    }

    fn try_inline_as_async_fn(&self, i_graph: &mut InlinedGraph<'g>, body_id: BodyId) -> bool {
        let local_def_id = body_id.into_local_def_id(self.tcx);
        let body_with_facts =
            borrowck_facts::get_simplified_body_with_borrowck_facts(self.tcx, local_def_id);
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

        let root_location = self.gli.globalize_location(return_location, body_id);

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
            self.tcx.def_path_debug_str(local_def_id.to_def_id())
        );
        self.inline_one_function(
            i_graph,
            body_id,
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
        }: &mut InlinedGraph<'g>,
        caller_function: BodyId,
        inlining_target: LocalDefId,
        incoming: &[(SimpleLocation<(GlobalLocation<'g>, DefId)>, Edge)],
        outgoing: &[(SimpleLocation<(GlobalLocation<'g>, DefId)>, Edge)],
        arguments: &[Option<mir::Local>],
        return_to: Option<mir::Local>,
        queue_for_pruning: &mut EdgeSet<'g>,
        root_location: GlobalLocation<'g>,
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

        let gli_here = self
            .gli
            .at(root_location.outermost_location(), caller_function);
        eqs.extend(
            Self::relativize_eqs(&grw_to_inline.equations, &gli_here).chain(
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

        let mut connect_to =
            |g: &mut GraphImpl<_>, source, target, weight: Edge, pruning_required| {
                let mut add_edge = |source, register_for_pruning| {
                    debug!("Connecting {source} -> {target}");
                    if register_for_pruning {
                        queue_for_pruning.insert((source, target));
                    }
                    add_weighted_edge(g, source, target, weight)
                };
                match source {
                    Node::Call((loc, did)) => add_edge(
                        Node::Call((gli_here.relativize(loc), did)),
                        pruning_required,
                    ),
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
            let new =
                old.map_call(|(location, function)| (gli_here.relativize(*location), *function));
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
        i_graph: &mut InlinedGraph<'g>,
        body_id: BodyId,
    ) -> EdgeSet<'g> {
        let recursive_analysis_enabled = self.ana_ctrl.use_recursive_analysis();
        let mut queue_for_pruning = HashSet::new();
        if recursive_analysis_enabled && self.try_inline_as_async_fn(i_graph, body_id) {
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
                    if let Some(ac) =
                        self.classify_special_function_handling(*function, id, &i_graph.graph)
                    {
                        return Some((id, *location, InlineAction::Drop(ac)));
                    }
                    if let Some(local_id) = function.as_local()
                        && self.marker_carrying.should_inline(local_id)
                        && (!self.ana_ctrl.avoid_inlining() || self.marker_carrying.marker_is_reachable(local_id))
                    {
                        debug!("Inlining {function:?}");
                        return Some((id, *location, InlineAction::SimpleInline(local_id)));
                    }
                }
                let local_as_global = GlobalLocal::at_root;
                let call = self.get_call(*location);
                debug!("Abstracting {function:?}");
                let fn_sig = self.tcx.fn_sig(function).skip_binder().skip_binder();
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
                        body_id,
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
    fn inline_graph(&self, body_id: BodyId) -> InlinedGraph<'g> {
        let proc_g = self.get_procedure_graph(body_id);
        let mut gwr = InlinedGraph::from_body(self.gli, body_id, proc_g, self.tcx);

        let name = body_name_pls(self.tcx, body_id).name;
        if self.dbg_ctrl.dump_pre_inline_graph() {
            dump_dot_graph(
                dump_file_pls(self.tcx, body_id, "pre-inline.gv").unwrap(),
                &gwr,
            )
            .unwrap();
        }
        if self.dbg_ctrl.dump_local_equations() {
            let mut eqout = dump_file_pls(self.tcx, body_id, "local.eqs").unwrap();
            for eq in &gwr.equations {
                use std::io::Write;
                writeln!(eqout, "{eq}").unwrap();
            }
        }

        let mut queue_for_pruning = time(&format!("Inlining subgraphs into '{name}'"), || {
            self.perform_subfunction_inlining(proc_g, &mut gwr, body_id)
        });

        if self.ana_ctrl.remove_inconsequential_calls().is_enabled() {
            panic!("Removing inconsequential calls is no longer supported");
        }

        if self.dbg_ctrl.dump_global_equations() {
            let mut eqout = dump_file_pls(self.tcx, body_id, "global.eqs").unwrap();
            for eq in &gwr.equations {
                use std::io::Write;
                writeln!(eqout, "{eq}").unwrap();
            }
        }
        if self.dbg_ctrl.dump_inlined_graph() {
            dump_dot_graph(
                dump_file_pls(self.tcx, body_id, "inlined.gv").unwrap(),
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
            self.prune_impossible_edges(
                &mut gwr,
                name,
                &edges_to_prune,
                body_id.into_local_def_id(self.tcx),
            );
            if self.dbg_ctrl.dump_inlined_pruned_graph() {
                dump_dot_graph(
                    dump_file_pls(self.tcx, body_id, "inlined-pruned.gv").unwrap(),
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

impl<'tcx, 'g> Inliner<'tcx, 'g> {
    /// Turn the output of the inliner into the format the rest of the dfpp pipeline
    /// understands.
    pub fn to_call_only_flow<A: FnMut(ArgNum) -> GlobalLocation<'g>>(
        &self,
        InlinedGraph { graph: g, .. }: &InlinedGraph<'g>,
        mut mk_arg: A,
    ) -> crate::ir::CallOnlyFlow<GlobalLocation<'g>> {
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
