use crate::{
    ana::inline_judge::InlineJudge, ann::MarkerAnnotation, desc::*, discover::FnToAnalyze,
    stats::TimedStat, utils::*, DefId, HashMap, HashSet, MarkerCtx,
};
use flowistry_pdg::SourceUse;
use paralegal_spdg::{Node, SPDGStats};
use rustc_hir::{def, def_id::LocalDefId};
use rustc_middle::{
    mir::{self, Location},
    ty::{self, Instance, TyCtxt},
};

use std::{cell::RefCell, fmt::Display, rc::Rc, time::Instant};

use super::{
    default_index, path_for_item, src_loc_for_span, BodyInfo, RustcInstructionKind, SPDGGenerator,
};
use anyhow::{anyhow, bail, Result};
use either::Either;
use flowistry_pdg_construction::{
    graph::{DepEdge, DepEdgeKind, DepGraph, DepNode},
    CallChangeCallback, CallChanges, CallInfo, InlineMissReason,
    SkipCall::Skip,
};
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
    local_def_id: DefId,

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
}

impl<'a, 'tcx, C: Extend<DefId>> GraphConverter<'tcx, 'a, C> {
    /// Initialize a new converter by creating an initial PDG using flowistry.
    pub fn new_with_flowistry(
        generator: &'a SPDGGenerator<'tcx>,
        known_def_ids: &'a mut C,
        target: &'a FnToAnalyze,
    ) -> Result<Self> {
        let local_def_id = target.def_id;
        let start = Instant::now();
        let dep_graph = Self::create_flowistry_graph(generator, local_def_id)?;

        if generator.opts.dbg().dump_flowistry_pdg() {
            dep_graph.generate_graphviz(format!(
                "{}.flowistry-pdg.pdf",
                generator.tcx.def_path_str(target.def_id)
            ))?
        }

        Ok(Self {
            generator,
            known_def_ids,
            target,
            index_map: vec![default_index(); dep_graph.graph.node_bound()].into(),
            dep_graph: dep_graph.into(),
            local_def_id,
            types: Default::default(),
            spdg: Default::default(),
            marker_assignments: Default::default(),
        })
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.generator.tcx
    }

    fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        self.generator.marker_ctx()
    }

    /// Is the top-level function (entrypoint) an `async fn`
    fn entrypoint_is_async(&self) -> bool {
        self.generator
            .flowistry_loader
            .get_asyncness(self.local_def_id)
            .is_async()
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
    fn node_annotations(&mut self, old_node: Node, weight: &DepNode<'tcx>) {
        let leaf_loc = weight.at.leaf();
        let node = self.new_node_for(old_node);

        let graph = self.dep_graph.clone();

        let body = self
            .generator
            .flowistry_loader
            .get_body_info(leaf_loc.function)
            .unwrap();

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
                let instruction = body.instruction_at(loc);
                if let RustcInstructionKind::FunctionCall(f) = instruction.kind {
                    self.known_def_ids.extend(Some(f.id));

                    // Question: Could a function with no input produce an
                    // output that has aliases? E.g. could some place, where the
                    // local portion isn't the local from the destination of
                    // this function call be affected/modified by this call? If
                    // so, that location would also need to have this marker
                    // attached
                    let needs_return_markers = graph
                        .graph
                        .edges_directed(old_node, Direction::Incoming)
                        .any(|e| {
                            let at = e.weight().at;
                            #[cfg(debug_assertions)]
                            assert_edge_location_invariant(self.tcx(), at, body, weight.at);
                            weight.at == at && e.weight().target_use.is_return()
                        });

                    if needs_return_markers {
                        self.register_annotations_for_function(node, f.id, |ann| {
                            ann.refinement.on_return()
                        });
                    }

                    for e in graph.graph.edges_directed(old_node, Direction::Outgoing) {
                        let SourceUse::Argument(arg) = e.weight().source_use else {
                            continue;
                        };
                        self.register_annotations_for_function(node, f.id, |ann| {
                            ann.refinement.on_argument().contains(arg as u32).unwrap()
                        });
                    }
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
    ) -> Option<mir::tcx::PlaceTy<'tcx>> {
        let tcx = self.tcx();
        let body = self
            .generator
            .flowistry_loader
            .get_body_info(at.leaf().function)
            .unwrap();
        let generics = self.generator.flowistry_loader.get_mono(at);

        // So actually we're going to check the base place only, because
        // Flowistry sometimes tracks subplaces instead but we want the marker
        // from the base place.
        let place = if self.entrypoint_is_async() && place.local.as_u32() == 1 && at.len() == 2 {
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

        let raw_ty = place.ty(body, tcx);
        Some(
            *FnResolution::Final(
                Instance::resolve(
                    tcx,
                    ty::ParamEnv::reveal_all(),
                    at.leaf().function,
                    generics,
                )
                .unwrap()
                .unwrap(),
            )
            .try_monomorphize(tcx, ty::ParamEnv::reveal_all(), &raw_ty),
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
                .map(|ann| Identifier::new_intern(ann.marker.as_str())),
        );
        self.known_def_ids.extend(parent);
    }

    /// Check if this node is of a marked type and register that type.
    fn handle_node_types(&mut self, old_node: Node, weight: &DepNode<'tcx>) {
        let i = self.new_node_for(old_node);

        let Some(place_ty) = self.determine_place_type(weight.at, weight.place.as_ref()) else {
            return;
        };
        let deep = !weight.is_split;
        let mut node_types = self.type_is_marked(place_ty, deep).collect::<HashSet<_>>();
        for (p, _) in weight.place.iter_projections() {
            if let Some(place_ty) = self.determine_place_type(weight.at, p) {
                node_types.extend(self.type_is_marked(place_ty, false));
            }
        }
        self.known_def_ids.extend(node_types.iter().copied());
        let tcx = self.tcx();
        if !node_types.is_empty() {
            self.types
                .entry(i)
                .or_default()
                .extend(node_types.iter().filter(|t| match tcx.def_kind(*t) {
                    def::DefKind::Generator => false,
                    kind => !kind.is_fn_like(),
                }))
        }
    }

    /// Create an initial flowistry graph for the function identified by
    /// `local_def_id`.
    fn create_flowistry_graph(
        generator: &SPDGGenerator<'tcx>,
        def_id: DefId,
    ) -> Result<DepGraph<'tcx>> {
        let tcx = generator.tcx;
        let opts = generator.opts;

        let Some(pdg) = generator.flowistry_loader.get_pdg(def_id) else {
            bail!("Failed to construct the graph");
        };

        Ok(pdg)
    }

    /// Consume the generator and compile the [`SPDG`].
    pub fn make_spdg(mut self) -> SPDG {
        let start = Instant::now();
        self.make_spdg_impl();
        let arguments = self.determine_arguments();
        let return_ = self.determine_return();
        SPDG {
            path: path_for_item(self.local_def_id, self.tcx()),
            graph: self.spdg,
            id: self.local_def_id,
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
        }
    }

    /// This initializes the fields `spdg` and `index_map` and should be called first
    fn make_spdg_impl(&mut self) {
        use petgraph::prelude::*;
        let g_ref = self.dep_graph.clone();
        let input = &g_ref.graph;
        let tcx = self.tcx();

        for (i, weight) in input.node_references() {
            let at = weight.at.leaf();

            self.register_node(
                i,
                NodeInfo {
                    at: weight.at,
                    description: format!("{:?}", weight.place),
                    span: src_loc_for_span(weight.span, tcx),
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

fn assert_edge_location_invariant<'tcx>(
    tcx: TyCtxt<'tcx>,
    at: CallString,
    body: &BodyInfo<'tcx>,
    location: CallString,
) {
    // Normal case. The edge is introduced where the operation happens
    if location == at {
        return;
    }
    // Control flow case. The edge is introduced at the `switchInt`
    if let RichLocation::Location(loc) = at.leaf().location {
        if at.leaf().function == location.leaf().function
            && matches!(
                body.instruction_at(loc).kind,
                RustcInstructionKind::SwitchInt
            )
        {
            return;
        }
    }
    let mut msg = tcx.sess.struct_span_fatal(
        body.span_of(at.leaf().location),
        format!(
            "This operation is performed in a different location: {}",
            at
        ),
    );
    msg.span_note(
        body.span_of(location.leaf().location),
        format!("Expected to originate here: {}", at),
    );
    msg.emit()
}

pub(super) struct MyCallback<'tcx> {
    pub(super) judge: InlineJudge<'tcx>,
    pub(super) stat_wrap: StatStracker,
    pub(super) tcx: TyCtxt<'tcx>,
}

impl<'tcx> CallChangeCallback<'tcx> for MyCallback<'tcx> {
    fn on_inline(&self, info: CallInfo<'tcx>) -> CallChanges {
        let mut changes = CallChanges::default();

        let mut skip = true;

        if is_non_default_trait_method(self.tcx, info.callee.def_id()).is_some() {
            self.tcx.sess.span_warn(
                self.tcx.def_span(info.callee.def_id()),
                "Skipping analysis of unresolvable trait method.",
            );
        } else if self.judge.should_inline(&info) {
            skip = false;
        };

        if skip {
            changes = changes.with_skip(Skip);
        } else {
            record_inlining(
                &self.stat_wrap,
                self.tcx,
                info.callee.def_id().expect_local(),
                info.is_cached,
            )
        }
        changes
    }

    fn on_inline_miss(
        &self,
        resolution: FnResolution<'tcx>,
        loc: Location,
        parent: FnResolution<'tcx>,
        call_string: Option<CallString>,
        reason: InlineMissReason,
    ) {
        let body = self
            .tcx
            .body_for_def_id(parent.def_id().expect_local())
            .unwrap();
        let span = body
            .body
            .stmt_at(loc)
            .either(|s| s.source_info.span, |t| t.source_info.span);
        let markers_reachable = self.judge.marker_ctx().get_reachable_markers(resolution);
        self.tcx.sess.span_err(
            span,
            format!(
                "Could not inline this function call in {:?}, at {} because {reason:?}. {}",
                parent.def_id(),
                call_string.map_or("root".to_owned(), |c| c.to_string()),
                Print(|f| if markers_reachable.is_empty() {
                    f.write_str("No markers are reachable")
                } else {
                    f.write_str("Markers ")?;
                    write_sep(f, ", ", markers_reachable.iter(), Display::fmt)?;
                    f.write_str(" are reachable")
                })
            ),
        );
    }
}

type StatStracker = Rc<RefCell<(SPDGStats, HashSet<LocalDefId>)>>;

fn record_inlining(tracker: &StatStracker, tcx: TyCtxt<'_>, def_id: LocalDefId, is_in_cache: bool) {
    let mut borrow = tracker.borrow_mut();
    let (stats, loc_set) = &mut *borrow;
    stats.inlinings_performed += 1;
    let is_new = loc_set.insert(def_id);

    if !is_new || is_in_cache {
        return;
    }

    let src_map = tcx.sess.source_map();
    let span = body_span(&tcx.body_for_def_id(def_id).unwrap().body);
    let (_, start_line, _, end_line, _) = src_map.span_to_location_info(span);
    let body_lines = (end_line - start_line + 1) as u32;
    if is_new {
        stats.unique_functions += 1;
        stats.unique_locs += body_lines;
    }
    if !is_in_cache {
        stats.analyzed_functions += 1;
        stats.analyzed_locs += body_lines;
    }
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
