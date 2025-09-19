use std::{marker::PhantomData, rc::Rc, time::Instant};

use self::call_string_resolver::CallStringResolver;
use super::{default_index, path_for_item, src_loc_for_span, SPDGGenerator};
use crate::{
    ann::MarkerAnnotation, desc::*, discover::FnToAnalyze, stats::TimedStat, utils::*, HashMap,
    HashSet, MarkerCtx, Pctx,
};
use flowistry_pdg::{rustc_portable::Location, SourceUse};
use flowistry_pdg_construction::{
    body_cache::BodyCache,
    call_tree_visit::{VisitDriver, Visitor},
    determine_async,
    graph::{DepEdge, DepEdgeKind, DepGraph, DepNode, OneHopLocation, PartialGraph},
    is_async_trait_fn, match_async_trait_assign,
    utils::{handle_shims, try_monomorphize, try_resolve_function, type_as_fn, ShimResult},
};
use paralegal_spdg::{Node, SPDGStats};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir,
    ty::{self, Instance, TyCtxt, TypingEnv},
};

use anyhow::Result;
use either::Either;
use flowistry::mir::FlowistryInput;
use petgraph::{
    visit::{IntoNodeReferences, NodeIndexable, NodeRef},
    Direction,
};

/// Structure responsible for converting one [`DepGraph`] into an [`SPDG`].
///
/// Intended usage is to call [`Self::new_with_flowistry`] to initialize, then
/// [`Self::make_spdg`] to convert.
pub struct GraphConverter<'tcx, 'a, C> {
    // Immutable information
    /// The parent generator
    generator: &'a SPDGGenerator<'tcx>,
    /// Information about the function this PDG belongs to
    target: &'a FnToAnalyze,
    /// The flowistry graph we are converting
    dep_graph: Rc<DepGraph<'tcx>>,
    /// Same as the ID stored in self.target, but as a local def id
    def_id: DefId,

    // Mutable fields
    /// Where we write every [`DefId`] we encounter into.
    known_def_ids: &'a mut C,
    /// A map of which nodes are of which (marked) type. We build this up during
    /// conversion.
    types: HashMap<Node, Vec<DefId>>,
    /// Mapping from old node indices to new node indices. Use
    /// [`Self::register_node`] to insert and [`Self::new_node_for`] to query.
    index_map: Box<[Node]>,
    /// The converted graph we are creating
    spdg: SPDGImpl,
    marker_assignments: HashMap<Node, HashSet<Identifier>>,
    call_string_resolver: call_string_resolver::CallStringResolver<'tcx>,
    stats: SPDGStats,
}

impl<'a, 'tcx, C: Extend<DefId>> GraphConverter<'tcx, 'a, C> {
    /// Initialize a new converter by creating an initial PDG using flowistry.
    pub fn new_with_flowistry(
        generator: &'a SPDGGenerator<'tcx>,
        known_def_ids: &'a mut C,
        target: &'a FnToAnalyze,
    ) -> Result<Self> {
        let local_def_id = target.def_id;
        let (dep_graph, stats) = generator.stats.measure(TimedStat::Flowistry, || {
            Self::create_flowistry_graph(generator, local_def_id)
        })?;

        log::info!("Flowistry graph created for {}", target.name());

        if generator.ctx.opts().dbg().dump_flowistry_pdg() {
            dep_graph.generate_graphviz(format!(
                "{}.flowistry-pdg.pdf",
                generator.tcx().def_path_str(target.def_id)
            ))?
        }

        let def_id = local_def_id.to_def_id();

        Ok(Self {
            generator,
            known_def_ids,
            target,
            index_map: vec![default_index(); dep_graph.graph.node_bound()].into(),
            dep_graph: dep_graph.into(),
            def_id,
            types: Default::default(),
            spdg: Default::default(),
            marker_assignments: Default::default(),
            call_string_resolver: CallStringResolver::new(generator.ctx.clone(), def_id),
            stats,
        })
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.generator.tcx()
    }

    fn ctx(&self) -> &Pctx<'tcx> {
        &self.generator.ctx
    }

    fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        self.generator.marker_ctx()
    }

    /// Is the top-level function (entrypoint) an `async fn`
    fn entrypoint_is_async(&self) -> bool {
        entrypoint_is_async(self.body_cache(), self.tcx(), self.def_id)
    }

    /// Insert this node into the converted graph, return it's auto-assigned id
    /// and register it as corresponding to `old` in the initial graph. Fails if
    /// there is already a node registered as corresponding to `old`.
    fn register_node(&mut self, old: Node, new: NodeInfo) -> Node {
        let new_node = self.spdg.add_node(new);
        let r = &mut self.index_map[old.index()];
        assert_eq!(*r, default_index());
        *r = new_node;
        new_node
    }

    /// Get the id of the new node that was registered for this old node.
    fn new_node_for(&self, old: Node) -> Node {
        let res = self.index_map[old.index()];
        assert_ne!(res, default_index());
        res
    }

    fn register_markers(&mut self, node: Node, markers: impl IntoIterator<Item = Identifier>) {
        let mut markers = markers.into_iter().peekable();

        if markers.peek().is_some() {
            self.marker_assignments
                .entry(node)
                .or_default()
                .extend(markers);
        }
    }

    /// Find direct annotations on this node and register them in the marker map.
    fn node_annotations(&mut self, old_node: Node, weight: &DepNode<'tcx, CallString>) {
        let leaf_loc = weight.at.leaf();
        let node = self.new_node_for(old_node);

        let body = self.body_cache().get(leaf_loc.function).body();

        let graph = self.dep_graph.clone();

        match leaf_loc.location {
            RichLocation::Start
                if matches!(body.local_kind(weight.place.local), mir::LocalKind::Arg) =>
            {
                let function_id = leaf_loc.function;
                let arg_num = weight.place.local.as_u32() - 1;
                self.known_def_ids.extend(Some(function_id));

                self.register_annotations_for_function(node, function_id, |ann| {
                    ann.refinement.on_argument().contains(arg_num).unwrap()
                });
            }
            RichLocation::End if weight.place.local == mir::RETURN_PLACE => {
                let function_id = leaf_loc.function;
                self.known_def_ids.extend(Some(function_id));
                self.register_annotations_for_function(node, function_id, |ann| {
                    ann.refinement.on_return()
                });
            }
            RichLocation::Location(loc) => {
                let crate::Either::Right(
                    term @ mir::Terminator {
                        kind: mir::TerminatorKind::Call { func, .. },
                        ..
                    },
                ) = body.stmt_at(loc)
                else {
                    return;
                };
                debug!("Assigning markers to {:?}", term.kind);
                let res = self.call_string_resolver.resolve(weight.at);
                let param_env = TypingEnv::post_analysis(self.tcx(), res.def_id());
                let func =
                    try_monomorphize(res, self.tcx(), param_env, func, term.source_info.span)
                        .unwrap();
                let Some(funcc) = func.constant() else {
                    self.ctx().maybe_span_err(
                        weight.span,
                        "SOUNDNESS: Cannot determine markers for function call",
                    );
                    return;
                };
                let (inst, args) = type_as_fn(self.tcx(), ty_of_const(funcc)).unwrap();
                let f = if let Some(inst) = try_resolve_function(
                    self.tcx(),
                    inst,
                    TypingEnv::post_analysis(self.tcx(), leaf_loc.function),
                    args,
                ) {
                    match handle_shims(inst, self.tcx(), param_env, weight.span) {
                        ShimResult::IsHandledShim { instance, .. } => instance,
                        ShimResult::IsNotShim => inst,
                        ShimResult::IsNonHandleableShim => {
                            self.ctx().maybe_span_err(
                                weight.span,
                                "SOUNDNESS: Cannot determine markers for shim usage",
                            );
                            return;
                        }
                    }
                    .def_id()
                } else {
                    debug!("Could not resolve {inst:?} properly during marker assignment");
                    inst
                };

                self.known_def_ids.extend(Some(f));

                // Question: Could a function with no input produce an
                // output that has aliases? E.g. could some place, where the
                // local portion isn't the local from the destination of
                // this function call be affected/modified by this call? If
                // so, that location would also need to have this marker
                // attached
                //
                // Also yikes. This should have better detection of whether
                // a place is (part of) a function return
                let mut in_edges = graph
                    .graph
                    .edges_directed(old_node, Direction::Incoming)
                    .filter(|e| e.weight().kind == DepEdgeKind::Data);

                let needs_return_markers = in_edges.clone().next().is_none()
                    || in_edges.any(|e| {
                        let at = e.weight().at;
                        #[cfg(debug_assertions)]
                        assert_edge_location_invariant(self.tcx(), at, body, weight.at, |cs| {
                            cs.leaf()
                        });
                        weight.at == at && e.weight().target_use.is_return()
                    });

                if needs_return_markers {
                    self.register_annotations_for_function(node, f, |ann| {
                        ann.refinement.on_return()
                    });
                }

                for e in graph.graph.edges_directed(old_node, Direction::Outgoing) {
                    let SourceUse::Argument(arg) = e.weight().source_use else {
                        continue;
                    };
                    self.register_annotations_for_function(node, f, |ann| {
                        ann.refinement.on_argument().contains(arg as u32).unwrap()
                    });
                }
            }
            _ => (),
        }
    }

    /// Reconstruct the type for the data this node represents.
    fn determine_place_type(
        &self,
        at: CallString,
        place: mir::PlaceRef<'tcx>,
        span: rustc_span::Span,
    ) -> Option<mir::tcx::PlaceTy<'tcx>> {
        let tcx = self.tcx();
        let locations = at.iter_from_root().collect::<Vec<_>>();
        let (last, mut rest) = locations.split_last().unwrap();

        if self.entrypoint_is_async() {
            let (first, tail) = rest.split_first().unwrap();
            // The body of a top-level `async` function binds a closure to the
            // return place `_0`. Here we expect are looking at the statement
            // that does this binding.
            assert!(expect_stmt_at(self.body_cache(), *first).is_left());
            rest = tail;
        }

        // So actually we're going to check the base place only, because
        // Flowistry sometimes tracks subplaces instead but we want the marker
        // from the base place.
        let place = if self.entrypoint_is_async() && place.local.as_u32() == 1 && rest.len() == 1 {
            if place.projection.is_empty() {
                return None;
            }
            // in the case of targeting the top-level async closure (e.g. async args)
            // we'll keep the first projection.
            mir::Place {
                local: place.local,
                projection: self.tcx().mk_place_elems(&place.projection[..1]),
            }
        } else {
            place.local.into()
        };

        let resolution = self.call_string_resolver.resolve(at);

        // Thread through each caller to recover generic arguments
        let body = self.body_cache().get(last.function);
        let raw_ty = place.ty(body.body(), tcx);
        Some(
            try_monomorphize(
                resolution,
                tcx,
                TypingEnv::fully_monomorphized(),
                &raw_ty,
                span,
            )
            .unwrap(),
        )
    }

    /// Fetch annotations item identified by this `id`.
    ///
    /// The callback is used to filter out annotations where the "refinement"
    /// doesn't match. The idea is that the caller of this function knows
    /// whether they are looking for annotations on an argument or return of a
    /// function identified by this `id` or on a type and the callback should be
    /// used to enforce this.
    fn register_annotations_for_function(
        &mut self,
        node: Node,
        function: DefId,
        mut filter: impl FnMut(&MarkerAnnotation) -> bool,
    ) {
        let parent = get_parent(self.tcx(), function);
        let marker_ctx = self.marker_ctx().clone();
        self.register_markers(
            node,
            marker_ctx
                .combined_markers(function)
                .chain(
                    parent
                        .into_iter()
                        .flat_map(|parent| marker_ctx.combined_markers(parent)),
                )
                .filter(|ann| filter(ann))
                .map(|ann| ann.marker),
        );
        self.known_def_ids.extend(parent);
    }

    /// Check if this node is of a marked type and register that type.
    fn handle_node_types(&mut self, old_node: Node, weight: &DepNode<'tcx, CallString>) {
        let i = self.new_node_for(old_node);

        let Some(place_ty) =
            self.determine_place_type(weight.at, weight.place.as_ref(), weight.span)
        else {
            return;
        };
        trace!("Node {:?} has place type {:?}", weight.place, place_ty);
        // Restore after fixing https://github.com/brownsys/paralegal/issues/138
        //let deep = !weight.is_split;
        let deep = true;
        let mut node_types = self.type_is_marked(place_ty, deep).collect::<HashSet<_>>();
        for (p, _) in weight.place.iter_projections() {
            if let Some(place_ty) = self.determine_place_type(weight.at, p, weight.span) {
                node_types.extend(self.type_is_marked(place_ty, false));
            }
        }
        self.known_def_ids.extend(node_types.iter().copied());
        let tcx = self.tcx();
        if !node_types.is_empty() {
            self.types.entry(i).or_default().extend(
                node_types
                    .iter()
                    .filter(|t| !tcx.is_coroutine(**t) && !tcx.def_kind(*t).is_fn_like()),
            )
        }
        trace!(
            "For node {:?} found marked node types {node_types:?}",
            weight.place
        );
    }

    /// Create an initial flowistry graph for the function identified by
    /// `local_def_id`.
    fn create_flowistry_graph(
        generator: &SPDGGenerator<'tcx>,
        local_def_id: LocalDefId,
    ) -> Result<(DepGraph<'tcx>, SPDGStats)> {
        let pdg = generator.pdg_constructor.construct_graph(local_def_id);

        Ok((pdg, Default::default()))
    }

    /// Consume the generator and compile the [`SPDG`].
    pub fn make_spdg(mut self) -> SPDG {
        let start = Instant::now();
        self.make_spdg_impl();
        let arguments = self.determine_arguments();
        let return_ = self.determine_return();
        self.generator
            .stats
            .record_timed(TimedStat::Conversion, start.elapsed());
        self.stats.conversion_time = start.elapsed();
        SPDG {
            path: path_for_item(self.def_id, self.tcx()),
            graph: self.spdg,
            id: self.def_id,
            name: Identifier::new(self.target.name()),
            arguments,
            markers: self
                .marker_assignments
                .into_iter()
                .map(|(k, v)| (k, v.into_iter().collect()))
                .collect(),
            return_,
            type_assigns: self
                .types
                .into_iter()
                .map(|(k, v)| (k, Types(v.into())))
                .collect(),
            statistics: self.stats,
        }
    }

    fn body_cache(&self) -> &BodyCache<'tcx> {
        self.generator.pdg_constructor.body_cache()
    }

    /// This initializes the fields `spdg` and `index_map` and should be called first
    fn make_spdg_impl(&mut self) {
        use petgraph::prelude::*;
        let g_ref = self.dep_graph.clone();
        let input = &g_ref.graph;
        let tcx = self.tcx();

        for (i, weight) in input.node_references() {
            let at = weight.at.leaf();
            let body = self.body_cache().get(at.function).body();

            let node_span = body.local_decls[weight.place.local].source_info.span;
            self.register_node(
                i,
                NodeInfo {
                    at: weight.at,
                    description: format!("{:?}", weight.place),
                    span: src_loc_for_span(node_span, tcx),
                    local: weight.place.local.as_u32(),
                },
            );
            self.node_annotations(i, weight);

            self.handle_node_types(i, weight);
        }

        for e in input.edge_references() {
            let DepEdge {
                kind,
                at,
                source_use,
                target_use,
            } = *e.weight();
            self.spdg.add_edge(
                self.new_node_for(e.source()),
                self.new_node_for(e.target()),
                EdgeInfo {
                    at,
                    kind: match kind {
                        DepEdgeKind::Control => EdgeKind::Control,
                        DepEdgeKind::Data => EdgeKind::Data,
                    },
                    source_use,
                    target_use,
                },
            );
        }
    }

    /// Return the (sub)types of this type that are marked.
    fn type_is_marked(
        &'a self,
        typ: mir::tcx::PlaceTy<'tcx>,
        deep: bool,
    ) -> impl Iterator<Item = TypeId> + 'a {
        if deep {
            Either::Left(self.marker_ctx().deep_type_markers(typ.ty).iter().copied())
        } else {
            Either::Right(self.marker_ctx().shallow_type_markers(typ.ty))
        }
        .map(|(d, _)| d)
    }

    /// Similar to `CallString::is_at_root`, but takes into account top-level
    /// async functions
    fn try_as_root(&self, at: CallString) -> Option<GlobalLocation> {
        if self.entrypoint_is_async() && at.len() == 2 {
            at.iter_from_root().nth(1)
        } else if at.is_at_root() {
            Some(at.leaf())
        } else {
            None
        }
    }

    /// Try to find the node corresponding to the values returned from this
    /// controller.
    ///
    /// TODO: Include mutable inputs
    fn determine_return(&self) -> Box<[Node]> {
        // In async functions
        self.spdg
            .node_references()
            .filter(|n| {
                let weight = n.weight();
                let at = weight.at;
                matches!(self.try_as_root(at), Some(l) if l.location == RichLocation::End)
            })
            .map(|n| n.id())
            .collect()
    }

    /// Determine the set if nodes corresponding to the inputs to the
    /// entrypoint. The order is guaranteed to be the same as the source-level
    /// function declaration.
    fn determine_arguments(&self) -> Box<[Node]> {
        let mut g_nodes: Vec<_> = self
            .dep_graph
            .graph
            .node_references()
            .filter(|n| {
                let at = n.weight().at;
                let is_candidate =
                    matches!(self.try_as_root(at), Some(l) if l.location == RichLocation::Start);
                is_candidate
            })
            .collect();

        g_nodes.sort_by_key(|(_, i)| i.place.local);

        g_nodes
            .into_iter()
            .map(|n| self.new_node_for(n.id()))
            .collect()
    }
}

fn dep_edge_kind_to_edge_kind(kind: DepEdgeKind) -> EdgeKind {
    match kind {
        DepEdgeKind::Control => EdgeKind::Control,
        DepEdgeKind::Data => EdgeKind::Data,
    }
}

#[cfg(debug_assertions)]
fn assert_edge_location_invariant<'tcx, Loc: Eq + std::fmt::Display>(
    tcx: TyCtxt<'tcx>,
    at: Loc,
    body: &mir::Body<'tcx>,
    location: Loc,
    leaf: impl Fn(&Loc) -> GlobalLocation,
) {
    // Normal case. The edge is introduced where the operation happens
    if location == at {
        return;
    }
    // Control flow case. The edge is introduced at the `switchInt`
    if let RichLocation::Location(loc) = leaf(&at).location {
        if leaf(&at).function == leaf(&location).function
            && matches!(
                body.stmt_at(loc),
                Either::Right(mir::Terminator {
                    kind: mir::TerminatorKind::SwitchInt { .. },
                    ..
                })
            )
        {
            return;
        }
    }
    let mut msg = tcx.dcx().struct_span_fatal(
        (body, leaf(&at).location).span(tcx),
        format!(
            "This operation is performed in a different location: {}",
            at
        ),
    );
    msg.span_note(
        (body, leaf(&location).location).span(tcx),
        format!("Expected to originate here: {}", at),
    );
    msg.emit()
}

/// Find the statement at this location or fail.
fn expect_stmt_at<'tcx>(
    body_cache: &BodyCache<'tcx>,
    loc: GlobalLocation,
) -> Either<&'tcx mir::Statement<'tcx>, &'tcx mir::Terminator<'tcx>> {
    let body = &body_cache.get(loc.function).body();
    let RichLocation::Location(loc) = loc.location else {
        unreachable!();
    };
    body.stmt_at(loc)
}

/// If `did` is a method of an `impl` of a trait, then return the `DefId` that
/// refers to the method on the trait definition.
fn get_parent(tcx: TyCtxt, did: DefId) -> Option<DefId> {
    let ident = tcx.opt_item_ident(did)?;
    let kind = match tcx.def_kind(did) {
        kind if kind.is_fn_like() => ty::AssocKind::Fn,
        // todo allow constants and types also
        _ => return None,
    };
    let r#impl = tcx.impl_of_method(did)?;
    let r#trait = tcx.trait_id_of_impl(r#impl)?;
    let id = tcx
        .associated_items(r#trait)
        .find_by_name_and_kind(tcx, ident, kind, r#trait)?
        .def_id;
    Some(id)
}

fn entrypoint_is_async<'tcx>(
    body_cache: &BodyCache<'tcx>,
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> bool {
    tcx.asyncness(def_id).is_async()
        || is_async_trait_fn(tcx, def_id, body_cache.get(def_id).body())
}

mod call_string_resolver {
    //! Resolution of [`CallString`]s to [`FnResolution`]s.
    //!
    //! This is a separate mod so that we can use encapsulation to preserve the
    //! internal invariants of the resolver.

    use flowistry_pdg::CallString;
    use flowistry_pdg_construction::utils::{
        manufacture_substs_for, try_monomorphize, try_resolve_function,
    };
    use paralegal_spdg::Endpoint;
    use rustc_middle::{
        mir::TerminatorKind,
        ty::{Instance, TypingEnv},
    };
    use rustc_utils::cache::Cache;

    use crate::{Either, Pctx};

    use super::{func_of_term, map_either, match_async_trait_assign, AsFnAndArgs};

    /// Cached resolution of [`CallString`]s to [`Instance`]s.
    ///
    /// Only valid for a single controller. Each controller should initialize a
    /// new resolver.
    pub struct CallStringResolver<'tcx> {
        cache: Cache<CallString, Instance<'tcx>>,
        ctx: Pctx<'tcx>,
        entrypoint_is_async: bool,
    }

    impl<'tcx> CallStringResolver<'tcx> {
        /// Tries to resolve to the monomophized function in which this call
        /// site exists. That is to say that `return.def_id() ==
        /// cs.leaf().function`.
        ///
        /// Unlike `Self::resolve_internal` this can be called on any valid
        /// [`CallString`].
        pub fn resolve(&self, cs: CallString) -> Instance<'tcx> {
            let tcx = self.ctx.tcx();
            let (this, opt_prior_loc) = cs.pop();
            if let Some(prior_loc) = opt_prior_loc {
                if prior_loc.len() != 1 || !self.entrypoint_is_async {
                    return self.resolve_internal(prior_loc);
                }
            }
            let def_id = this.function;
            try_resolve_function(
                tcx,
                def_id,
                TypingEnv::post_analysis(tcx, def_id).with_post_analysis_normalized(tcx),
                manufacture_substs_for(tcx, def_id).unwrap(),
            )
            .unwrap()
        }

        pub fn new(ctx: Pctx<'tcx>, entrypoint: Endpoint) -> Self {
            Self {
                cache: Default::default(),
                entrypoint_is_async: super::entrypoint_is_async(
                    ctx.body_cache(),
                    ctx.tcx(),
                    entrypoint,
                ),
                ctx,
            }
        }

        /// This resolves the monomorphized function *being called at* this call
        /// site.
        ///
        /// This function is internal because it panics if `cs.leaf().location`
        /// is not either a function call or a statement where an async closure
        /// is created and assigned.
        fn resolve_internal(&self, cs: CallString) -> Instance<'tcx> {
            *self.cache.get(&cs, |_| {
                let this = cs.leaf();
                let prior = self.resolve(cs);

                let tcx = self.ctx.tcx();

                let base_stmt = super::expect_stmt_at(self.ctx.body_cache(), this);
                let param_env = TypingEnv::post_analysis(tcx, prior.def_id())
                    .with_post_analysis_normalized(tcx);
                let normalized = map_either(
                    base_stmt,
                    |stmt| {
                        try_monomorphize(prior, tcx, param_env, stmt, stmt.source_info.span)
                            .unwrap()
                    },
                    |term| {
                        try_monomorphize(prior, tcx, param_env, term, term.source_info.span)
                            .unwrap()
                    },
                );
                let res = match normalized {
                    Either::Right(term) => {
                        let (def_id, args) = func_of_term(tcx, &term).unwrap();
                        let instance = Instance::expect_resolve(
                            tcx,
                            param_env,
                            def_id,
                            args,
                            term.source_info.span,
                        );
                        if let Some(model) = self.ctx.marker_ctx().has_stub(def_id) {
                            let TerminatorKind::Call { args, .. } = &term.kind else {
                                unreachable!()
                            };
                            model
                                .apply(tcx, instance, param_env, args, term.source_info.span)
                                .unwrap()
                                .0
                        } else {
                            term.as_instance_and_args(tcx).unwrap().0
                        }
                    }
                    Either::Left(stmt) => {
                        let (def_id, generics) = match_async_trait_assign(&stmt).unwrap();
                        try_resolve_function(tcx, def_id, param_env, generics).unwrap()
                    }
                };
                res
            })
        }
    }
}

struct GraphAssembler<'tcx, 'a> {
    def_id: DefId,
    graph: SPDGImpl,
    // nodes: FxHashMap<DepNode<'tcx, CallString>, petgraph::graph::NodeIndex>,
    // control_inputs: Box<[(NodeIndex, DepEdge<CallString>)]>,
    nodes: FxHashMap<NodeInfo, petgraph::graph::NodeIndex>,
    control_inputs: Box<[(Node, EdgeInfo)]>,
    marker_assignments: HashMap<Node, HashSet<Identifier>>,
    known_def_ids: &'a mut FxHashSet<DefId>,
    /// A map of which nodes are of which (marked) type. We build this up during
    /// conversion.
    types: HashMap<Node, Vec<DefId>>,
    generator: &'a SPDGGenerator<'tcx>,
}

pub fn assemble_pdg<'tcx, 'a>(
    generator: &'a SPDGGenerator<'tcx>,
    known_def_ids: &'a mut FxHashSet<DefId>,
    target: &'a FnToAnalyze,
) -> SPDG {
    let tcx = generator.tcx();
    let def_id = target.def_id.to_def_id();
    let base_body = generator
        .pdg_constructor
        .body_cache()
        .try_get(def_id)
        .unwrap_or_else(|| {
            panic!("INVARIANT VIOLATED: body for local function {def_id:?} cannot be loaded.",)
        })
        .body();
    let async_state = determine_async(tcx, def_id, base_body);

    let base_function_id = async_state.map_or(def_id, |(generator, ..)| generator.def_id());

    let (instance, k) = generator
        .pdg_constructor
        .create_root_key(base_function_id.expect_local());
    let mut driver = VisitDriver::new(&generator.pdg_constructor, instance, k);
    let mut assembler = GraphAssembler::new(generator, known_def_ids, target.def_id.to_def_id());
    if let Some((generator, loc, ..)) = async_state {
        driver.with_pushed_stack(
            GlobalLocation {
                function: def_id,
                location: RichLocation::Location(loc),
            },
            |driver| {
                driver.start(&mut assembler);
                let pgraph = driver.current_graph_as_rc();
                let args_as_nodes = base_body
                    .args_iter()
                    .map(|arg| {
                        DepNode::new(
                            arg.into(),
                            OneHopLocation {
                                location: RichLocation::Start,
                                in_child: None,
                            },
                            tcx,
                            base_body,
                            def_id,
                            false,
                        )
                    })
                    .collect::<Vec<_>>();
                let return_node = DepNode::new(
                    mir::RETURN_PLACE.into(),
                    OneHopLocation {
                        location: RichLocation::End,
                        in_child: None,
                    },
                    tcx,
                    base_body,
                    def_id,
                    false,
                );
                for n in pgraph.iter_nodes() {
                    let generator_loc = RichLocation::Location(loc);
                    let relocated_n = |start_or_end| {
                        n.map_at(|_| OneHopLocation {
                            location: generator_loc,
                            in_child: Some((generator.def_id(), start_or_end)),
                        })
                    };

                    if n.place.local.as_u32() != 1 && n.at.location == RichLocation::Start {
                        let Some(mir::ProjectionElem::Field(id, _)) = n.place.projection.first()
                        else {
                            tcx.dcx().span_err(
                                n.span,
                                "Expected field projection on async generator in {def_id:?}",
                            );
                            continue;
                        };

                        let arg = &args_as_nodes[id.as_usize()];
                        assert!(false, "TODO remap location of n");
                        assembler.visit_edge(
                            driver,
                            arg,
                            &relocated_n(true),
                            &DepEdge {
                                kind: DepEdgeKind::Data,
                                at: OneHopLocation {
                                    location: generator_loc,
                                    in_child: None,
                                },
                                source_use: SourceUse::Argument(id.as_u32() as u8),
                                target_use: TargetUse::Assign,
                            },
                        );
                    } else if n.place.local == mir::RETURN_PLACE {
                        assembler.visit_edge(
                            driver,
                            &relocated_n(true),
                            &return_node,
                            &DepEdge {
                                kind: DepEdgeKind::Data,
                                at: OneHopLocation {
                                    location: generator_loc,
                                    in_child: None,
                                },
                                source_use: SourceUse::Operand,
                                target_use: TargetUse::Return,
                            },
                        );
                    }
                }
            },
        );
    } else {
        driver.start(&mut assembler);
    }
    let return_ = assembler.determine_return();
    let arguments = assembler.determine_arguments();
    let graph = assembler.graph;
    SPDG {
        name: Identifier::new(target.name()),
        path: path_for_item(target.def_id.to_def_id(), tcx),
        id: target.def_id.to_def_id(),
        graph,
        markers: assembler
            .marker_assignments
            .into_iter()
            .map(|(node, markers)| (node, markers.into_iter().collect()))
            .collect(),
        arguments,
        return_,
        type_assigns: assembler
            .types
            .into_iter()
            .map(|(k, v)| (k, Types(v.into())))
            .collect(),
        statistics: Default::default(),
    }
}

impl<'tcx, 'a> GraphAssembler<'tcx, 'a> {
    fn new(
        generator: &'a SPDGGenerator<'tcx>,
        known_def_ids: &'a mut FxHashSet<DefId>,
        def_id: DefId,
    ) -> Self {
        Self {
            def_id,
            graph: SPDGImpl::new(),
            nodes: Default::default(),
            control_inputs: Box::new([]),
            marker_assignments: Default::default(),
            known_def_ids,
            types: Default::default(),
            generator,
        }
    }

    fn register_markers(&mut self, node: Node, markers: impl IntoIterator<Item = Identifier>) {
        let mut markers = markers.into_iter().peekable();

        if markers.peek().is_some() {
            self.marker_assignments
                .entry(node)
                .or_default()
                .extend(markers);
        }
    }

    fn add_node(&mut self, node: NodeInfo) -> petgraph::graph::NodeIndex {
        *self
            .nodes
            .entry(node.clone())
            .or_insert_with(|| self.graph.add_node(node))
    }

    /// Forwarding of control flow. It is sound to replace the control inputs
    /// here rather than extend them because we are guaranteed that these new
    /// nodes are connected to the old ctrl nodes, possibly transitively.
    ///
    /// Each node in our graph is either connected to a local control flow
    /// node or to the ones coming from the parent, which is established by
    /// the `visit_partial_graph` function. By induction all nodes, including
    /// these control flow sources are connected to the old ctrl inputs.
    fn with_new_ctr_inputs<'c, F, R, K: Clone>(
        &mut self,
        vis: &mut VisitDriver<'tcx, 'c, K>,
        new_ctrl_inputs: &[(DepNode<'tcx, OneHopLocation>, DepEdge<OneHopLocation>)],
        f: F,
    ) -> R
    where
        F: FnOnce(&mut Self, &mut VisitDriver<'tcx, 'c, K>) -> R,
    {
        let new_ctrl_inputs: Box<[(Node, EdgeInfo)]> = new_ctrl_inputs
            .iter()
            .map(|(src, edge)| {
                let src = globalize_node(vis, src, self.tcx());
                let src_idx = self.add_node(src);
                let new_edge = globalize_edge(vis, edge);
                (src_idx, new_edge)
            })
            .collect();
        // The last thing we need to ensure for that to hold is that the new
        // ctrl inputs must not be empty. So if they are we leave the old one's intact.
        let old_ctrl_inputs = if new_ctrl_inputs.is_empty() {
            Box::new([])
        } else {
            std::mem::replace(&mut self.control_inputs, new_ctrl_inputs)
        };
        let r = f(self, vis);
        if !old_ctrl_inputs.is_empty() {
            self.control_inputs = old_ctrl_inputs;
        }
        r
    }

    fn ctx(&self) -> &Pctx<'tcx> {
        &self.generator.ctx
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx().tcx()
    }

    fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        self.generator.marker_ctx()
    }

    /// Fetch annotations item identified by this `id`.
    ///
    /// The callback is used to filter out annotations where the "refinement"
    /// doesn't match. The idea is that the caller of this function knows
    /// whether they are looking for annotations on an argument or return of a
    /// function identified by this `id` or on a type and the callback should be
    /// used to enforce this.
    fn register_annotations_for_function(
        &mut self,
        node: Node,
        function: DefId,
        mut filter: impl FnMut(&MarkerAnnotation) -> bool,
    ) {
        let parent = get_parent(self.tcx(), function);
        let marker_ctx = self.marker_ctx().clone();
        self.register_markers(
            node,
            marker_ctx
                .combined_markers(function)
                .chain(
                    parent
                        .into_iter()
                        .flat_map(|parent| marker_ctx.combined_markers(parent)),
                )
                .filter(|ann| filter(ann))
                .map(|ann| ann.marker),
        );
        self.known_def_ids.extend(parent);
    }

    fn node_annotations<K: Clone>(
        &mut self,
        node: Node,
        weight: &DepNode<'tcx, OneHopLocation>,
        vis: &VisitDriver<'tcx, '_, K>,
    ) {
        if weight.at.in_child.is_some() {
            // Transition nodes are handled again in the child right?
            return;
        }
        let leaf_loc = weight.at.location;
        let function = vis.current_function();
        let function_id = function.def_id();

        let body = self
            .generator
            .pdg_constructor
            .body_cache()
            .get(function.def_id())
            .body();

        match leaf_loc {
            RichLocation::Start
                if matches!(body.local_kind(weight.place.local), mir::LocalKind::Arg) =>
            {
                let arg_num = weight.place.local.as_u32() - 1;
                self.known_def_ids.extend(Some(function_id));

                self.register_annotations_for_function(node, function_id, |ann| {
                    ann.refinement.on_argument().contains(arg_num).unwrap()
                });
            }
            RichLocation::End if weight.place.local == mir::RETURN_PLACE => {
                self.known_def_ids.extend(Some(function_id));
                self.register_annotations_for_function(node, function_id, |ann| {
                    ann.refinement.on_return()
                });
            }
            RichLocation::Location(loc) => {
                let crate::Either::Right(
                    term @ mir::Terminator {
                        kind: mir::TerminatorKind::Call { func, .. },
                        ..
                    },
                ) = body.stmt_at(loc)
                else {
                    return;
                };
                debug!("Assigning markers to {:?}", term.kind);
                let res = function;
                let param_env = TypingEnv::post_analysis(self.tcx(), res.def_id());
                let func =
                    try_monomorphize(res, self.tcx(), param_env, func, term.source_info.span)
                        .unwrap();
                let Some(funcc) = func.constant() else {
                    self.generator.ctx.maybe_span_err(
                        weight.span,
                        "SOUNDNESS: Cannot determine markers for function call",
                    );
                    return;
                };
                let (inst, args) = type_as_fn(self.tcx(), ty_of_const(funcc)).unwrap();
                let f = if let Some(inst) = try_resolve_function(
                    self.tcx(),
                    inst,
                    TypingEnv::post_analysis(self.tcx(), function_id),
                    args,
                ) {
                    match handle_shims(inst, self.tcx(), param_env, weight.span) {
                        ShimResult::IsHandledShim { instance, .. } => instance,
                        ShimResult::IsNotShim => inst,
                        ShimResult::IsNonHandleableShim => {
                            self.ctx().maybe_span_err(
                                weight.span,
                                "SOUNDNESS: Cannot determine markers for shim usage",
                            );
                            return;
                        }
                    }
                    .def_id()
                } else {
                    debug!("Could not resolve {inst:?} properly during marker assignment");
                    inst
                };

                self.known_def_ids.extend(Some(f));

                let graph = vis.current_graph();

                // Question: Could a function with no input produce an
                // output that has aliases? E.g. could some place, where the
                // local portion isn't the local from the destination of
                // this function call be affected/modified by this call? If
                // so, that location would also need to have this marker
                // attached
                //
                // Also yikes. This should have better detection of whether
                // a place is (part of) a function return

                let mut is_return_use = false;
                let mut has_no_data_edges = true;

                for (from, to, edge_weight) in graph.iter_edges() {
                    if from == weight {
                        let SourceUse::Argument(arg) = edge_weight.source_use else {
                            continue;
                        };
                        self.register_annotations_for_function(node, f, |ann| {
                            ann.refinement.on_argument().contains(arg as u32).unwrap()
                        });
                    } else if to == weight && edge_weight.kind == DepEdgeKind::Data {
                        has_no_data_edges = false;
                        let at = edge_weight.at.clone();
                        #[cfg(debug_assertions)]
                        assert_edge_location_invariant(
                            self.tcx(),
                            at.clone(),
                            body,
                            weight.at.clone(),
                            |at| GlobalLocation {
                                function: function.def_id(),
                                location: at.location,
                            },
                        );
                        if weight.at == at && edge_weight.target_use.is_return() {
                            is_return_use = true;
                        }
                    }
                }
                let needs_return_markers = has_no_data_edges | is_return_use;

                if needs_return_markers {
                    self.register_annotations_for_function(node, f, |ann| {
                        ann.refinement.on_return()
                    });
                }
            }
            _ => (),
        }
    }

    /// Determine the set if nodes corresponding to the inputs to the
    /// entrypoint. The order is guaranteed to be the same as the source-level
    /// function declaration.
    fn determine_arguments(&self) -> Box<[Node]> {
        let mut g_nodes: Vec<_> = self
            .graph
            .node_references()
            .filter(|n| {
                let at = n.weight().at;
                let is_candidate =
                    matches!(self.try_as_root(at), Some(l) if l.location == RichLocation::Start);
                is_candidate
            })
            .collect();

        g_nodes.sort_by_key(|(_, i)| i.local);

        g_nodes.into_iter().map(|(n, _)| n).collect()
    }

    /// Try to find the node corresponding to the values returned from this
    /// controller.
    ///
    /// TODO: Include mutable inputs
    fn determine_return(&self) -> Box<[Node]> {
        // In async functions
        self.graph
            .node_references()
            .filter(|n| {
                let weight = n.weight();
                let at = weight.at;
                matches!(self.try_as_root(at), Some(l) if l.location == RichLocation::End)
            })
            .map(|n| n.id())
            .collect()
    }

    /// Similar to `CallString::is_at_root`, but takes into account top-level
    /// async functions
    fn try_as_root(&self, at: CallString) -> Option<GlobalLocation> {
        if self.entrypoint_is_async() && at.len() == 2 {
            at.iter_from_root().nth(1)
        } else if at.is_at_root() {
            Some(at.leaf())
        } else {
            None
        }
    }

    /// Is the top-level function (entrypoint) an `async fn`
    fn entrypoint_is_async(&self) -> bool {
        entrypoint_is_async(
            self.generator.pdg_constructor.body_cache(),
            self.tcx(),
            self.def_id,
        )
    }
}

fn globalize_node<'tcx, K: Clone>(
    vis: &mut VisitDriver<'tcx, '_, K>,
    node: &DepNode<'tcx, OneHopLocation>,
    tcx: TyCtxt<'tcx>,
) -> NodeInfo {
    let at = vis.globalize_location(&node.at);
    NodeInfo {
        at,
        description: format!("{:?}", node.place),
        span: src_loc_for_span(node.span, tcx),
        local: node.place.local.as_u32(),
    }
}

fn globalize_edge<K: Clone>(
    vis: &mut VisitDriver<'_, '_, K>,
    edge: &DepEdge<OneHopLocation>,
) -> EdgeInfo {
    let at = vis.globalize_location(&edge.at);
    EdgeInfo {
        kind: dep_edge_kind_to_edge_kind(edge.kind),
        at,
        source_use: edge.source_use,
        target_use: edge.target_use,
    }
}

impl<'tcx, 'a, K: std::hash::Hash + Eq + Clone> Visitor<'tcx, K> for GraphAssembler<'tcx, 'a> {
    fn visit_inlined_call(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_, K>,
        loc: Location,
        inst: Instance<'tcx>,
        k: &K,
        ctrl_inputs: &[(DepNode<'tcx, OneHopLocation>, DepEdge<OneHopLocation>)],
    ) {
        self.with_new_ctr_inputs(vis, ctrl_inputs, |slf, vis| {
            vis.visit_inlined_call(slf, loc, inst, k)
        })
    }

    fn visit_node(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_, K>,
        node: &DepNode<'tcx, OneHopLocation>,
    ) {
        let idx = self.add_node(globalize_node(vis, node, self.tcx()));
        self.node_annotations(idx, node, vis);
    }

    fn visit_edge(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_, K>,
        src: &DepNode<'tcx, OneHopLocation>,
        dst: &DepNode<'tcx, OneHopLocation>,
        kind: &DepEdge<OneHopLocation>,
    ) {
        let src = globalize_node(vis, src, self.tcx());
        let src_idx = self.add_node(src);
        let dst = globalize_node(vis, dst, self.tcx());
        let dst_idx = self.add_node(dst);
        let new_kind = globalize_edge(vis, kind);
        self.graph.add_edge(src_idx, dst_idx, new_kind);
    }

    fn visit_partial_graph(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_, K>,
        graph: &PartialGraph<'tcx, K>,
    ) {
        vis.visit_partial_graph(self, graph);

        // This loop connects the control inputs that
        // are incoming to the function to those nodes in the graph who have no
        // control inputs yet.
        //
        // We do this here instead of in "visit_node", because that gets called
        // before the "visit_edge" function, meaning we can't yet see the
        // potential control inputs of the node. We could have the visitor use
        // an opposite ordering, but that is counterintuitive to other potential
        // users of the visitor.
        for node in graph.iter_nodes() {
            let new_node = globalize_node(vis, node, self.tcx());
            let node = self.add_node(new_node);

            if !self
                .graph
                .edges_directed(node, petgraph::Direction::Incoming)
                .any(|e| e.weight().is_control())
            {
                for (src, edge) in self.control_inputs.iter() {
                    self.graph.add_edge(*src, node, edge.clone());
                }
            }
        }
    }
}
