use super::{path_for_item, src_loc_for_span};
use crate::{
    ann::{db::AutoMarkers, side_effect_detection},
    desc::*,
    utils::*,
    HashMap, HashSet, MarkerCtx, Pctx,
};
use flowistry_pdg::rustc_portable::Location;
use flowistry_pdg_construction::{
    determine_async,
    utils::{handle_shims, try_monomorphize, try_resolve_function, type_as_fn, ShimResult},
    DepEdge, DepEdgeKind, DepNode, DepNodeKind, MemoPdgConstructor, OneHopLocation, PartialGraph,
    Use, VisitDriver, Visitor,
};
use paralegal_spdg::Node;

use rustc_hash::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir,
    ty::{Instance, TyCtxt, TypingEnv},
};

use either::Either;
use flowistry::mir::FlowistryInput;
use petgraph::visit::{IntoNodeReferences, NodeRef};

fn dep_edge_kind_to_edge_kind(kind: DepEdgeKind) -> EdgeKind {
    match kind {
        DepEdgeKind::Control => EdgeKind::Control,
        DepEdgeKind::Data => EdgeKind::Data,
    }
}

struct GraphAssembler<'tcx, 'a> {
    // read-only information
    pctx: Pctx<'tcx>,
    is_async: bool,

    // Translation helpers
    /// Translation tables for nodes from local PartialGraphs to the global PDG
    nodes: Vec<Vec<GNode>>,

    // Incrementally built information
    graph: SPDGImpl,
    marker_assignments: HashMap<GNode, HashSet<Identifier>>,
    /// A map of which nodes are of which (marked) type. We build this up during
    /// conversion.
    types: HashMap<GNode, Vec<DefId>>,
    known_def_ids: &'a mut FxHashSet<DefId>,
}

/// Create a global PDG (spanning the entire call tree) starting from the given
/// target function.
pub fn assemble_pdg<'tcx>(
    pctx: &Pctx<'tcx>,
    pdg_constructor: &MemoPdgConstructor<'tcx, u32>,
    known_def_ids: &mut FxHashSet<DefId>,
    target: DefId,
) -> SPDG {
    let tcx = pctx.tcx();

    // Information and body of the provided target function
    let base_body_def_id = target;
    let base_body = pctx
        .body_cache()
        .try_get(base_body_def_id)
        .unwrap_or_else(|| {
            panic!("INVARIANT VIOLATED: body for local function {base_body_def_id:?} cannot be loaded.",)
        })
        .body();

    let async_state = determine_async(tcx, base_body_def_id, base_body);

    // These will refer to the function we are actually analyzing from, which may
    // be a generator if the target is async.
    let possibly_generator_id =
        async_state.map_or(base_body_def_id, |(generator, ..)| generator.def_id());
    let (possible_generator_instance, k) =
        pdg_constructor.create_root_key(possibly_generator_id.expect_local());

    let mut driver = VisitDriver::new(pdg_constructor, possible_generator_instance, k);
    let mut assembler = GraphAssembler::new(pctx.clone(), known_def_ids, base_body_def_id);

    // If the top level function is async we start analysis from the generator
    // instead (because the async function itself is basically empty, it just
    // creates the generator object).
    if let Some((_, loc, ..)) = async_state {
        // If the top-level function is async we place that on the call stack
        // first so it shows up in the call strings that are generated for the
        // nodes.
        driver.with_pushed_stack(
            GlobalLocation {
                function: base_body_def_id,
                location: RichLocation::Location(loc),
            },
            |driver| {
                driver.start(&mut assembler);
            },
        );
        // Using create_root_key might seem weird here but it currently does what
        // we need (resolve the instance)
        let base_instance = pdg_constructor
            .create_root_key(base_body_def_id.expect_local())
            .0;
        // Because we actually started the analysis from the generator, we now
        // have to manually sync up the actual arguments to the async function.
        assembler.fix_async_args(base_instance, loc, &mut driver);
    } else {
        driver.start(&mut assembler);
    }
    let return_ = assembler.determine_return();
    let arguments = assembler.determine_arguments();
    let graph = assembler.graph;
    SPDG {
        name: Identifier::new(tcx.opt_item_ident(base_body_def_id).unwrap().name),
        path: path_for_item(base_body_def_id, tcx),
        id: base_body_def_id,
        graph,
        markers: assembler
            .marker_assignments
            .into_iter()
            .map(|(GNode(node), markers)| (node, markers.into_iter().collect()))
            .collect(),
        arguments,
        return_,
        type_assigns: assembler
            .types
            .into_iter()
            .map(|(GNode(k), v)| (k, Types(v.into())))
            .collect(),
        statistics: Default::default(),
    }
}

impl<'tcx, 'a> GraphAssembler<'tcx, 'a> {
    fn new(pctx: Pctx<'tcx>, known_def_ids: &'a mut FxHashSet<DefId>, def_id: DefId) -> Self {
        let is_async = entrypoint_is_async(pctx.body_cache(), pctx.tcx(), def_id);
        Self {
            graph: SPDGImpl::new(),
            pctx,
            nodes: Default::default(),
            marker_assignments: Default::default(),
            known_def_ids,
            types: Default::default(),
            is_async,
        }
    }

    /// Add these markers to our marker table we maintain for nodes.
    fn register_markers(&mut self, node: GNode, markers: impl IntoIterator<Item = Identifier>) {
        let mut markers = markers.into_iter().peekable();

        if markers.peek().is_some() {
            self.marker_assignments
                .entry(node)
                .or_default()
                .extend(markers);
        }
    }

    /// Add a node from the current local graph to the global graph. Returns the
    /// global index. If the node was already added, returns the prior index.
    fn add_node<K: Clone>(
        &mut self,
        node: Node,
        vis: &mut VisitDriver<'tcx, '_, K>,
        weight: &DepNode<'tcx, OneHopLocation>,
    ) -> GNode {
        let weight = globalize_node(vis, weight, self.tcx());
        let table = self.nodes.last_mut().unwrap();
        let prior = table[node.index()];
        if GNode(Node::end()) != prior {
            prior
        } else {
            let my_idx = GNode(self.graph.add_node(weight));
            table[node.index()] = my_idx;
            my_idx
        }
    }

    /// Add a node that does not correspond to any local graph. This is only used
    /// when fixing async args.
    fn add_untranslatable_node(
        &mut self,
        place: mir::Place,
        at: CallString,
        span: rustc_span::Span,
        is_arg: Option<u16>,
    ) -> GNode {
        GNode(self.graph.add_node(NodeInfo {
            at,
            kind: NodeKind::Place {
                description: format!("{place:?}"),
                local: place.local.as_u32(),
            },
            span: src_loc_for_span(span, self.tcx()),
            is_arg,
        }))
    }

    fn ctx(&self) -> &Pctx<'tcx> {
        &self.pctx
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx().tcx()
    }

    fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        self.pctx.marker_ctx()
    }

    // /// Fetch annotations item identified by this `id`.
    // ///
    // /// The callback is used to filter out annotations where the "refinement"
    // /// doesn't match. The idea is that the caller of this function knows
    // /// whether they are looking for annotations on an argument or return of a
    // /// function identified by this `id` or on a type and the callback should be
    // /// used to enforce this.
    // fn register_annotations_for_function(
    //     &mut self,
    //     node: GNode,
    //     function: DefId,
    //     mut filter: impl FnMut(&MarkerAnnotation) -> bool,
    // ) {
    //     let parent = get_parent(self.tcx(), function);
    //     let marker_ctx = self.marker_ctx().clone();
    //     self.register_markers(
    //         node,
    //         marker_ctx
    //             .combined_markers(function)
    //             .chain(
    //                 parent
    //                     .into_iter()
    //                     .flat_map(|parent| marker_ctx.combined_markers(parent)),
    //             )
    //             .filter(|ann| filter(ann))
    //             .map(|ann| ann.marker),
    //     );
    //     self.known_def_ids.extend(parent);
    // }

    /// Check if this node is of a marked type and register that type.
    fn handle_node_types<K: Clone>(
        &mut self,
        node: GNode,
        at: &OneHopLocation,
        place: mir::Place<'tcx>,
        span: rustc_span::Span,
        vis: &VisitDriver<'tcx, '_, K>,
    ) {
        trace!("Checking types for node {node:?} ({:?})", place);

        let tcx = self.tcx();
        let function = vis.current_function();

        // So actually we're going to check the base place only, because
        // Flowistry sometimes tracks subplaces instead but we want the marker
        // from the base place.
        let (base_place, projections) =
            if self.entrypoint_is_async() && place.local.as_u32() == 1 && at.in_child.is_none() {
                if place.projection.is_empty() {
                    return;
                }
                let (base_project, rest) = place.projection.split_first().unwrap();
                // in the case of targeting the top-level async closure (e.g. async args)
                // we'll keep the first projection.
                (
                    mir::Place {
                        local: place.local,
                        projection: self.tcx().mk_place_elems(&[*base_project]),
                    },
                    rest,
                )
            } else {
                (place.local.into(), place.projection.as_slice())
            };
        trace!("Using base place {base_place:?} with projections {projections:?}");

        let resolution = vis.current_function();

        // Thread through each caller to recover generic arguments
        let body = self.pctx.body_cache().get(function.def_id()).body();
        let raw_ty = base_place.ty(body, tcx);
        let base_ty = try_monomorphize(
            resolution,
            tcx,
            TypingEnv::fully_monomorphized(),
            &raw_ty,
            span,
        )
        .unwrap();

        self.handle_node_types_helper(node, base_ty, projections);
    }

    /// Adds the markers for all levels of projection on this node. For the
    /// final projection we add all markers from that type (deep markers), for
    /// others we only add the shallow markers.
    fn handle_node_types_helper(
        &mut self,
        node: GNode,
        mut base_ty: mir::tcx::PlaceTy<'tcx>,
        projections: &[mir::PlaceElem<'tcx>],
    ) {
        trace!("Has place type {base_ty:?}");
        let mut node_types = HashSet::new();
        for proj in projections {
            node_types.extend(self.type_is_marked(base_ty, false));
            base_ty = base_ty.projection_ty(self.tcx(), *proj);
        }
        node_types.extend(self.type_is_marked(base_ty, true));
        self.known_def_ids.extend(node_types.iter().copied());
        let tcx = self.tcx();
        if !node_types.is_empty() {
            self.types.entry(node).or_default().extend(
                node_types
                    .iter()
                    .filter(|t| !tcx.is_coroutine(**t) && !tcx.def_kind(*t).is_fn_like()),
            )
        }
        trace!("Found marked node types {node_types:?}",);
    }

    /// Return the (sub)types of this type that are marked.
    fn type_is_marked(
        &'a self,
        typ: mir::tcx::PlaceTy<'tcx>,
        deep: bool,
    ) -> impl Iterator<Item = TypeId> + use<'a, 'tcx> {
        if deep {
            Either::Left(self.marker_ctx().deep_type_markers(typ.ty).iter().copied())
        } else {
            Either::Right(self.marker_ctx().shallow_type_markers(typ.ty))
        }
        .map(|(d, _)| d)
    }

    /// Discover and register directly applied markers on this node.
    fn node_annotations<K: Clone>(
        &mut self,
        node: GNode,
        weight: &DepNode<'tcx, OneHopLocation>,
        vis: &VisitDriver<'tcx, '_, K>,
    ) {
        let leaf_loc = weight.at.location;
        let function = vis.current_function();
        let function_id = function.def_id();

        let body = self.pctx.body_cache().get(function.def_id()).body();

        let ctx = self.marker_ctx().clone();
        match (leaf_loc, weight.place()) {
            (RichLocation::Start, Some(place))
                if matches!(body.local_kind(place.local), mir::LocalKind::Arg) =>
            {
                let arg_num = place.local.as_u32() - 1;
                self.known_def_ids.extend([function_id]);
                self.register_markers(node, ctx.markers_on_argument(function_id, arg_num as u16))
            }
            (RichLocation::End, Some(place)) if place.local == mir::RETURN_PLACE => {
                self.known_def_ids.extend([function_id]);
                self.register_markers(node, ctx.markers_on_return(function_id))
            }
            (RichLocation::Location(loc), _) => {
                self.handle_node_annotations_for_regular_location(node, weight, body, loc, vis);
            }
            _ => (),
        }
    }

    fn auto_markers(&self) -> &AutoMarkers {
        self.pctx.marker_ctx().auto_markers()
    }

    // XXX: This code duplicates the auto-marker assignment logic from
    // MarkerCtx::terminator_reachable_markers and
    // MarkerCtx::get_reachable_markers but really there should be only one
    // source of truth.
    /// Helper for `node_annotations` to handle the case where the node is at a `RichLocation::Location`.
    fn handle_node_annotations_for_regular_location<K: Clone>(
        &mut self,
        node: GNode,
        weight: &DepNode<'tcx, OneHopLocation>,
        body: &mir::Body<'tcx>,
        loc: Location,
        vis: &VisitDriver<'tcx, '_, K>,
    ) {
        let function = vis.current_function();
        let function_id = function.def_id();
        let side_effects =
            side_effect_detection::analyze_statement(body, loc, self.auto_markers(), self.tcx());
        if !side_effects.is_empty() {
            self.register_markers(node, side_effects);
        }
        let crate::Either::Right(
            term @ mir::Terminator {
                kind: mir::TerminatorKind::Call { func, .. },
                ..
            },
        ) = body.stmt_at(loc)
        else {
            return;
        };
        debug!(
            "Assigning markers to {:?} in {:?}",
            weight.place(),
            term.kind
        );
        let param_env = TypingEnv::post_analysis(self.tcx(), function.def_id());
        let func =
            try_monomorphize(function, self.tcx(), param_env, func, term.source_info.span).unwrap();
        let Some(funcc) = func.constant() else {
            self.pctx.maybe_span_err(
                weight.span,
                "SOUNDNESS: Cannot determine markers for function call",
            );
            self.register_markers(node, [self.auto_markers().side_effect_unknown_fn_ptr]);
            return;
        };
        let (inst, args) = type_as_fn(self.tcx(), ty_of_const(funcc)).unwrap();
        let minst = if let Some(inst) = try_resolve_function(
            self.tcx(),
            inst,
            TypingEnv::post_analysis(self.tcx(), function_id),
            args,
        ) {
            Some(
                match handle_shims(inst, self.tcx(), param_env, weight.span) {
                    ShimResult::IsHandledShim { instance, .. } => instance,
                    ShimResult::IsNotShim => inst,
                    ShimResult::IsNonHandleableShim => {
                        self.ctx().maybe_span_err(
                            weight.span,
                            "SOUNDNESS: Cannot determine markers for shim usage",
                        );
                        self.register_markers(node, [self.auto_markers().side_effect_unknown]);
                        return;
                    }
                },
            )
        } else {
            None
        };
        let f = minst.map_or_else(
            || {
                debug!("Could not resolve {inst:?} properly during marker assignment");
                self.register_markers(node, [self.auto_markers().side_effect_unknown]);
                inst
            },
            |i| i.def_id(),
        );

        self.known_def_ids.extend(Some(f));

        self.known_def_ids.extend(get_parent(self.tcx(), f));
        let ctx = self.marker_ctx().clone();
        match weight.use_ {
            _ if minst.is_some_and(|inst| {
                side_effect_detection::is_allowed_as_clone_unit_instance(self.tcx(), inst)
            }) => {}
            Use::Arg(arg) => self.register_markers(node, ctx.markers_on_argument(f, arg)),
            Use::Return => self.register_markers(node, ctx.markers_on_return(f)),
            Use::Other => (),
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
            .filter_map(|(n, i)| match i.kind {
                NodeKind::Place { local, .. } => Some((n, local)),
                _ => None,
            })
            .collect();

        g_nodes.sort_by_key(|(_, i)| *i);

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
        at.is_at_root().then(|| at.leaf())
    }

    /// Is the top-level function (entrypoint) an `async fn`
    fn entrypoint_is_async(&self) -> bool {
        self.is_async
    }

    /// When we analyze an async function (as entry point), we actually start
    /// the analysis from the generator, since the async function itself is
    /// mostly empty. However the arguments to the generator are not the same as
    /// for the async function. It is the generator object that basically
    /// tuples together the arguments to the original async function. (And as a
    /// second argument there's a context object.)
    ///
    /// This function adds nodes for the original async function's arguments and
    /// connects them to the fields of the generator object to establish the flows.
    fn fix_async_args<K: Clone + std::hash::Hash + Eq>(
        &mut self,
        instance: Instance<'tcx>,
        loc: Location,
        driver: &mut VisitDriver<'tcx, 'a, K>,
    ) {
        let def_id = instance.def_id();
        self.known_def_ids.extend([def_id]);
        let tcx = self.pctx.tcx();
        let base_body = self
            .pctx
            .body_cache()
            .try_get(def_id)
            .unwrap_or_else(|| {
                panic!("INVARIANT VIOLATED: body for local function {def_id:?} cannot be loaded.",)
            })
            .body();
        let pgraph = driver.current_graph_as_rc();

        // New nodes for arguments and return place
        let args_as_nodes = base_body
            .args_iter()
            .map(|arg| {
                self.add_untranslatable_node(
                    arg.into(),
                    driver.globalize_location(&RichLocation::Start.into()),
                    base_body.local_decls[arg].source_info.span,
                    Some((arg.as_u32() - 1) as u16),
                )
            })
            .collect::<Vec<_>>();
        let return_node = self.add_untranslatable_node(
            mir::RETURN_PLACE.into(),
            driver.globalize_location(&RichLocation::End.into()),
            base_body.local_decls[mir::RETURN_PLACE].source_info.span,
            None,
        );

        let mono_ty = |local| {
            let decl = &base_body.local_decls[local];
            mir::tcx::PlaceTy::from_ty(
                try_monomorphize(
                    instance,
                    tcx,
                    TypingEnv::fully_monomorphized(),
                    &decl.ty,
                    decl.source_info.span,
                )
                .unwrap(),
            )
        };

        let ctx = self.marker_ctx().clone();
        // Register the new nodes and add potential markers
        for (arg_num, a) in args_as_nodes.iter().enumerate() {
            self.register_markers(*a, ctx.markers_on_argument(def_id, arg_num as u16));
            let local = mir::Local::from_usize(arg_num + 1);
            self.handle_node_types_helper(*a, mono_ty(local), &[]);
        }
        self.register_markers(return_node, ctx.markers_on_return(def_id));
        let local = mir::RETURN_PLACE;
        self.handle_node_types_helper(return_node, mono_ty(local), &[]);

        // Establish connections to existing nodes
        let generator_loc = RichLocation::Location(loc);
        let transition_at = CallString::new(&[GlobalLocation {
            location: generator_loc,
            function: def_id,
        }]);
        for (nidx, n) in pgraph.iter_nodes() {
            let DepNode {
                kind: DepNodeKind::Place(n),
                at,
                span,
                ..
            } = n
            else {
                continue;
            };
            if n.place.local.as_u32() == 1 && at.location == RichLocation::Start {
                let ridx = self.translate_node(nidx);
                let Some(mir::ProjectionElem::Field(id, _)) = n.place.projection.first() else {
                    tcx.dcx().span_err(
                        *span,
                        format!("Expected field projection on async generator in {def_id:?}, found {:?}", n.place),
                    );
                    continue;
                };

                let arg = args_as_nodes[id.as_usize()];
                self.graph.add_edge(
                    arg.to_index(),
                    ridx.to_index(),
                    EdgeInfo {
                        kind: EdgeKind::Data,
                        at: transition_at,
                    },
                );
            } else if n.place.local == mir::RETURN_PLACE {
                let ridx = self.translate_node(nidx);
                self.graph.add_edge(
                    ridx.to_index(),
                    return_node.to_index(),
                    EdgeInfo {
                        kind: EdgeKind::Data,
                        at: transition_at,
                    },
                );
            }
        }
    }

    /// Translate a node from the current local graph to the global graph.
    fn translate_node(&self, node: Node) -> GNode {
        self.translate_node_in(node, self.nodes.len() - 1)
    }

    /// Translate a node from a specific local graph to the global graph.
    fn translate_node_in(&self, node: Node, index: usize) -> GNode {
        let idx = self.nodes[index][node.index()];
        assert_ne!(idx.to_index(), Node::end(), "Node {node:?} is unknown");
        idx
    }

    fn with_new_translation_table<R>(&mut self, size: usize, f: impl FnOnce(&mut Self) -> R) -> R {
        self.nodes.push(vec![GNode(Node::end()); size]);
        let result = f(self);
        if self.nodes.len() != 1 {
            // Yuck. In oder to still be able to fix up the async args we let
            // the bottom translation table remain.
            assert_eq!(self.nodes.pop().unwrap().len(), size);
        }
        result
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
        span: src_loc_for_span(node.span, tcx),
        kind: match &node.kind {
            DepNodeKind::Const(value) => NodeKind::Constant(*value),
            DepNodeKind::Place(pkind) => NodeKind::Place {
                description: format!("{:?}", pkind.place),
                local: pkind.place.local.as_u32(),
            },
        },
        is_arg: node.use_.as_arg(),
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
    }
}

/// A newtype for indices into the global graph. This type exists because under
/// the hood local and global graphs use the same index types which makes it
/// very easy to mistake them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GNode(petgraph::graph::NodeIndex);

impl GNode {
    fn to_index(self) -> petgraph::graph::NodeIndex {
        self.0
    }
}

impl<'tcx, K: std::hash::Hash + Eq + Clone> Visitor<'tcx, K> for GraphAssembler<'tcx, '_> {
    fn visit_parent_connection(
        &mut self,
        _vis: &mut VisitDriver<'tcx, '_, K>,
        in_caller: Node,
        in_this: Node,
        _is_at_start: bool,
    ) {
        let [parent_table, this_table] = self.nodes.last_chunk_mut().unwrap();
        this_table[in_this.index()] = parent_table[in_caller.index()]
    }

    fn visit_node(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_, K>,
        k: Node,
        node: &DepNode<'tcx, OneHopLocation>,
    ) {
        let is_in_child = node.at.in_child.is_some();
        let idx = self.add_node(k, vis, node);
        if !is_in_child {
            self.node_annotations(idx, node, vis);
            if let DepNodeKind::Place(p) = &node.kind {
                self.handle_node_types(idx, &node.at, p.place, node.span, vis);
            }
        }
    }

    fn visit_edge(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_, K>,
        src: Node,
        dst: Node,
        kind: &DepEdge<OneHopLocation>,
    ) {
        let src = self.translate_node(src);
        let dst = self.translate_node(dst);
        let new_kind = globalize_edge(vis, kind);
        self.graph
            .add_edge(src.to_index(), dst.to_index(), new_kind);
    }

    fn visit_partial_graph(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_, K>,
        graph: &PartialGraph<'tcx, K>,
    ) {
        self.with_new_translation_table(graph.node_count(), |slf: &mut Self| {
            trace!(
                "Visiting partial graph {:?}",
                slf.tcx().def_path_str(graph.def_id())
            );
            vis.visit_partial_graph(slf, graph);
        })
    }

    fn visit_ctrl_edge(
        &mut self,
        _vis: &mut VisitDriver<'tcx, '_, K>,
        index: usize,
        src: Node,
        dst: Node,
        edge: &DepEdge<CallString>,
    ) {
        let src = self.translate_node_in(src, index);
        let dst = self.translate_node(dst);
        self.graph.add_edge(
            src.to_index(),
            dst.to_index(),
            EdgeInfo {
                kind: dep_edge_kind_to_edge_kind(edge.kind),
                at: edge.at,
            },
        );
    }
}
