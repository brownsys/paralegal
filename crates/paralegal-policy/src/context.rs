use std::collections::BTreeMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::time::{Duration, Instant};
use std::vec;
use std::{io::Write, process::exit, sync::Arc};

pub use paralegal_spdg::rustc_portable::{DefId, LocalDefId};
use paralegal_spdg::traverse::{
    generic_flows_to, generic_influencees, generic_influencers, EdgeSelection,
};
use paralegal_spdg::{
    CallString, DefKind, DisplayNode, Endpoint, FunctionHandling, GlobalNode, HashMap, HashSet,
    Identifier, InstructionInfo, IntoIterGlobalNodes, NodeCluster, NodeInfo, ProgramDescription,
    Span, TypeId, SPDG,
};

use anyhow::{anyhow, bail, Result};
use itertools::{Either, Itertools};
use petgraph::visit::{EdgeRef, IntoNeighborsDirected, Reversed, Topo, Walker};
use petgraph::Direction::Outgoing;
use petgraph::{Direction, Incoming};

use crate::algo::flows_to::CtrlFlowsTo;

use crate::diagnostics::HasDiagnosticsBase;
use crate::Diagnostics;
use crate::{assert_warning, diagnostics::DiagnosticsRecorder};

/// User-defined PDG markers.
pub type Marker = Identifier;

/// The type identifying a function that is used in call sites.
pub type FunctionId = DefId;

/// Identifier for a graph element that allows attaching a marker.
pub type MarkableId = GlobalNode;

type MarkerIndex = HashMap<Marker, MarkerTargets>;
type FlowsTo = HashMap<Endpoint, CtrlFlowsTo>;

/// Collection of entities a particular marker has been applied to
#[derive(Clone, Debug, Default)]
pub struct MarkerTargets {
    types: Vec<TypeId>,
    nodes: Vec<MarkableId>,
}

impl MarkerTargets {
    /// List of types marked with a particular marker
    pub fn types(&self) -> &[TypeId] {
        self.types.as_slice()
    }

    /// List of graph nodes marked with a particular marker
    pub fn nodes(&self) -> &[MarkableId] {
        self.nodes.as_slice()
    }
}

use self::private::Sealed;

/// Interface for defining policies.
///
/// Holds a PDG ([`Self::desc`]) and defines basic queries like
/// [`Self::all_nodes_for_ctrl`] and combinators such as
/// [`Self::always_happens_before`]. These should be composed into more complex
/// policies.
///
/// To communicate the results of your policies with the user you can emit
/// diagnostic messages. To communicate a policy failure use
/// [`error`](crate::Diagnostics::error) or the [`crate::assert_error`] macro. To
/// communicate suspicious circumstances that are not outright cause for failure
/// use [`warning`](crate::Diagnostics::warning) or [`assert_warning`]. For all
/// types of errors, including those with span information for a particular
/// node, see the [`crate::Diagnostics`] trait.
///
/// Note that these methods just queue the diagnostics messages. To emit them
/// (and potentially terminate the program if the policy does not hold) use
/// [`Self::emit_diagnostics`]. If you used
/// [`super::GraphLocation::with_context`] this will be done automatically for
/// you.
#[derive(Debug)]
pub struct RootContext {
    marker_to_ids: MarkerIndex,
    desc: ProgramDescription,
    flows_to: Option<FlowsTo>,
    pub(crate) diagnostics: DiagnosticsRecorder,
    name_map: HashMap<Identifier, Vec<DefId>>,
    pub(crate) config: Arc<super::Config>,
    pub(crate) stats: ContextStats,
}

#[doc(hidden)]
#[derive(Debug)]
pub struct ContextStats {
    pub pdg_construction: Option<Duration>,
    pub deserialization: Option<Duration>,
    pub precomputation: Duration,
}

impl RootContext {
    /// Construct a [`Context`] from a [`ProgramDescription`].
    ///
    /// This also precomputes some data structures like an index over markers.
    pub fn new(desc: ProgramDescription, config: super::Config) -> Self {
        // Must bind this first because we want to time how long it takes to build the indices.
        let start = Instant::now();
        let name_map = desc
            .def_info
            .iter()
            .map(|(k, v)| (v.name, *k))
            .into_group_map();
        let marker_to_ids = Self::build_index_on_markers(&desc);
        let flows_to = config
            .use_flows_to_index
            .then(|| Self::build_flows_to(&desc));
        // Make sure no expensive computation happens in the constructor call
        // below, otherwise the measurement of construction time will be off.
        Self {
            marker_to_ids,
            desc,
            flows_to,
            diagnostics: Default::default(),
            name_map,
            config: Arc::new(config),
            stats: ContextStats {
                pdg_construction: None,
                precomputation: start.elapsed(),
                deserialization: None,
            },
        }
    }

    #[doc(hidden)]
    pub fn context_stats(&self) -> &ContextStats {
        &self.stats
    }

    #[deprecated = "Use NodeExt::associated_call_site instead"]
    /// Find the call string for the statement or function that produced this node.
    pub fn associated_call_site(&self, node: GlobalNode) -> CallString {
        node.associated_call_site(self)
    }

    #[deprecated = "Use NodeQueries::consuming_call_sites instead"]
    /// Call sites that consume this node directly. E.g. the outgoing edges.
    pub fn consuming_call_sites(&self, node: GlobalNode) -> impl Iterator<Item = CallString> + '_ {
        node.consuming_call_sites(self)
    }

    /// Find all controllers that bare this name.
    ///
    /// This function is intended for use in writing test cases. Actual policies
    /// should generally refrain from working with controller names, other than
    /// printing them in error messages or for debugging. Policies contingent on
    /// controller names are likely unsound.
    pub fn controllers_by_name(&self, name: Identifier) -> impl Iterator<Item = Endpoint> + '_ {
        self.desc
            .controllers
            .iter()
            .filter(move |(_n, g)| g.name == name)
            .map(|t| *t.0)
    }

    /// Find a singular controller with this name.
    ///
    /// This function should only be used in tests as the same caveats apply as
    /// in [`Self::controllers_by_name`].
    ///
    /// ### Returns `Err`
    ///
    /// If there is not *exactly* one controller of this name.
    pub fn controller_by_name(&self, name: Identifier) -> Result<Endpoint> {
        let all = self.controllers_by_name(name).collect::<Vec<_>>();
        match all.as_slice() {
            [one] => Ok(*one),
            [] => bail!("Found no controller named '{name}'"),
            many => bail!("Found more than one controller named '{name}': {many:?}"),
        }
    }

    /// Find a type, controller or function id by its name.
    ///
    /// Since many often share the same name this can fail with too many
    /// candidates. To handle such cases use [`Self::find_by_path`] or
    /// [`Self::find_all_by_name`].
    pub fn find_by_name(&self, name: impl AsRef<str>) -> Result<DefId> {
        let name = name.as_ref();
        match self.find_all_by_name(name)? {
            [one] => Ok(*one),
            [] => bail!("Impossible, group cannot be empty ({name})"),
            _other => bail!("Too many candidates for name '{name}'"),
        }
    }

    /// Find all types, controllers and functions with this name.
    pub fn find_all_by_name(&self, name: impl AsRef<str>) -> Result<&[DefId]> {
        let name = Identifier::new_intern(name.as_ref());
        self.name_map
            .get(&name)
            .ok_or_else(|| anyhow!("Did not know the name {name}"))
            .map(Vec::as_slice)
    }

    /// Find a type, controller or function with this path.
    pub fn find_by_path(&self, path: impl AsRef<[Identifier]>) -> Result<DefId> {
        let slc = path.as_ref();
        let (name, path) = slc
            .split_last()
            .ok_or_else(|| anyhow!("Path must be at least of length 1"))?;
        let matching = self
            .name_map
            .get(name)
            .ok_or_else(|| anyhow!("Did not know the name {name}"))?;
        for candidate in matching.iter() {
            if self
                .desc()
                .def_info
                .get(candidate)
                .ok_or_else(|| anyhow!("Impossible"))?
                .path
                .as_ref()
                == path
            {
                return Ok(*candidate);
            }
        }
        Err(anyhow!("Found no candidate matching the path."))
    }

    /// Dispatch and drain all queued diagnostics, aborts the program if any of
    /// them demand failure.
    pub fn emit_diagnostics_may_exit(&self, w: impl Write) -> Result<()> {
        if !self.diagnostics.emit(w)? {
            exit(1)
        }
        Ok(())
    }

    /// Dispatch and drain all queued diagnostics without aborting the program.
    pub fn emit_diagnostics(&self, w: impl Write) -> std::io::Result<bool> {
        self.diagnostics.emit(w)
    }

    /// Returns all nodes that are in any of the PDGs
    pub fn all_nodes(&self) -> impl Iterator<Item = GlobalNode> + '_ {
        self.desc().controllers.iter().flat_map(|(id, spdg)| {
            let id = *id;
            spdg.graph
                .node_indices()
                .map(move |n| GlobalNode::from_local_node(id, n))
        })
    }

    /// Return nodes that satisfy the predicate and which have no ancestors that
    /// satisfy the same predicate.
    pub fn roots_where<'a>(
        &'a self,
        f: impl Fn(GlobalNode) -> bool + 'a,
    ) -> impl Iterator<Item = GlobalNode> + 'a {
        self.all_nodes()
            .filter(move |n| f(*n) && n.predecessors(self).all(|n| !f(n)))
    }

    /// Emit a warning if this marker was not found in the source code.
    pub fn report_marker_if_absent(&self, marker: Marker) {
        assert_warning!(
            *self,
            self.marker_to_ids.contains_key(&marker),
            format!("Marker {marker} is mentioned in the policy but not defined in source")
        )
    }

    fn build_index_on_markers(desc: &ProgramDescription) -> MarkerIndex {
        desc.controllers
            .values()
            .flat_map(|spdg| {
                spdg.markers.iter().flat_map(move |(&inner, anns)| {
                    anns.iter().map(move |marker| {
                        (
                            *marker,
                            Either::Left(GlobalNode::from_local_node(spdg.id, inner)),
                        )
                    })
                })
            })
            .chain(desc.type_info.iter().flat_map(|(k, v)| {
                v.markers
                    .iter()
                    .copied()
                    .zip(std::iter::repeat(Either::Right(*k)))
            }))
            .into_grouping_map()
            .fold(MarkerTargets::default(), |mut r, _k, v| {
                v.either(|node| r.nodes.push(node), |typ| r.types.push(typ));
                r
            })
    }

    fn build_flows_to(desc: &ProgramDescription) -> FlowsTo {
        desc.controllers
            .iter()
            .map(|(id, c)| (*id, CtrlFlowsTo::build(c)))
            .collect()
    }

    #[deprecated = "Use NodeQueries::flows_to instead"]
    /// Returns whether a node flows to a node through the configured edge type.
    ///
    /// Nodes do not flow to themselves. CallArgument nodes do flow to their respective CallSites.
    ///
    /// If you use flows_to with [`EdgeSelection::Control`], you might want to consider using [`Context::has_ctrl_influence`], which additionally considers intermediate nodes which the src node has data flow to and has ctrl influence on the sink.
    pub fn flows_to(
        &self,
        src: impl IntoIterGlobalNodes,
        sink: impl IntoIterGlobalNodes,
        edge_type: EdgeSelection,
    ) -> bool {
        src.flows_to(sink, self, edge_type)
    }

    /// Find the node that represents the `index`th argument of the controller
    /// `ctrl_id`.
    ///
    /// ### Returns `None`
    ///
    /// If the controller with this id does not exist *or* the controller has
    /// fewer than `index` arguments.
    pub fn controller_argument(&self, ctrl_id: Endpoint, index: u32) -> Option<GlobalNode> {
        let ctrl = self.desc.controllers.get(&ctrl_id)?;
        let inner = *ctrl.arguments.get(index as usize)?;

        Some(GlobalNode::from_local_node(ctrl_id, inner))
    }

    /// Returns whether there is direct control flow influence from influencer to sink, or there is some node which is data-flow influenced by `influencer` and has direct control flow influence on `target`. Or as expressed in code:
    ///
    /// `some n where self.flows_to(influencer, n, EdgeSelection::Data) && self.flows_to(n, target, EdgeSelection::Control)`.
    pub fn has_ctrl_influence(
        &self,
        influencer: impl IntoIterGlobalNodes + Sized + Copy,
        target: impl IntoIterGlobalNodes + Sized + Copy,
    ) -> bool {
        influencer.has_ctrl_influence(target, self)
    }

    /// Returns iterator over all Nodes that influence the given sink Node.
    ///
    /// Does not return the input node. A CallSite sink will return all of the associated CallArgument nodes.
    pub fn influencers(
        &self,
        sink: impl IntoIterGlobalNodes + Sized,
        edge_type: EdgeSelection,
    ) -> impl Iterator<Item = GlobalNode> + '_ {
        sink.influencers(self, edge_type).into_iter()
    }

    /// Returns iterator over all Nodes that are influenced by the given src Node.
    ///
    /// Does not return the input node. A CallArgument src will return the associated CallSite.
    pub fn influencees(
        &self,
        src: impl IntoIterGlobalNodes + Sized,
        edge_type: EdgeSelection,
    ) -> impl Iterator<Item = GlobalNode> + '_ {
        src.influencees(self, edge_type).into_iter()
    }

    #[deprecated = "Use NodeExt::types instead"]
    /// Get the type(s) of a Node.
    pub fn get_node_types(&self, node: GlobalNode) -> &[DefId] {
        node.types(self)
    }

    #[deprecated = "Use NodeExt::has_marker instead"]
    /// Returns whether the given Node has the marker applied to it directly or via its type.
    pub fn has_marker(&self, marker: Marker, node: GlobalNode) -> bool {
        node.has_marker(self, marker)
    }

    /// Returns all DataSources, DataSinks, and CallSites for a Controller as Nodes.
    pub fn all_nodes_for_ctrl(&self, ctrl_id: Endpoint) -> impl Iterator<Item = GlobalNode> + '_ {
        let ctrl = &self.desc.controllers[&ctrl_id];
        ctrl.graph
            .node_indices()
            .map(move |inner| GlobalNode::from_local_node(ctrl_id, inner))
    }

    /// Returns an iterator over the data sources within controller `c` that have type `t`.
    pub fn srcs_with_type(
        &self,
        ctrl_id: Endpoint,
        t: DefId,
    ) -> impl Iterator<Item = GlobalNode> + '_ {
        self.desc.controllers[&ctrl_id]
            .type_assigns
            .iter()
            .filter_map(move |(src, ids)| {
                ids.0
                    .contains(&t)
                    .then_some(GlobalNode::from_local_node(ctrl_id, *src))
            })
    }

    /// Returns an iterator over all nodes that do not have any influencers of the given edge_type.
    pub fn roots(
        &self,
        ctrl_id: Endpoint,
        edge_type: EdgeSelection,
    ) -> impl Iterator<Item = GlobalNode> + '_ {
        let g = &self.desc.controllers[&ctrl_id].graph;
        let filtered = &edge_type.filter_graph(g);

        let mut roots = vec![];
        let mut root_like = HashSet::new();

        // This could be more efficient. We don't have to continue traversing
        // from non-root-nodes
        for n in Topo::new(filtered).iter(filtered) {
            if filtered
                .neighbors_directed(n, Incoming)
                .any(|n| !root_like.contains(&n))
            {
                continue;
            }
            let w = g.node_weight(n).unwrap();
            if self.desc.instruction_info[&w.at.leaf()]
                .kind
                .is_function_call()
                || w.at.leaf().location.is_start()
            {
                roots.push(GlobalNode::from_local_node(ctrl_id, n));
            } else {
                root_like.insert(n);
            }
        }

        roots.into_iter()
    }

    /// Returns the input [`ProgramDescription`].
    pub fn desc(&self) -> &ProgramDescription {
        &self.desc
    }

    /// Returns all the type alias annotation for a given type
    pub fn otypes(&self, id: TypeId) -> &[TypeId] {
        self.desc()
            .type_info
            .get(&id)
            .map_or(&[], |info| info.otypes.as_ref())
    }

    /// Return all types that are marked with `marker`
    pub fn marked_type(&self, marker: Marker) -> &[DefId] {
        self.report_marker_if_absent(marker);
        self.marker_to_ids
            .get(&marker)
            .map_or(&[], |i| i.types.as_slice())
    }

    /// Return an example pair for a flow from an source from `from` to a sink
    /// in `to` if any exist.
    pub fn any_flows(
        &self,
        from: &[GlobalNode],
        to: &[GlobalNode],
        edge_type: EdgeSelection,
    ) -> Option<(GlobalNode, GlobalNode)> {
        from.iter().find_map(|src| {
            to.iter().find_map(|sink| {
                src.flows_to(*sink, self, edge_type)
                    .then_some((*src, *sink))
            })
        })
    }

    /// Iterate over all defined controllers
    pub fn all_controllers(&self) -> impl Iterator<Item = (Endpoint, &SPDG)> {
        self.desc().controllers.iter().map(|(k, v)| (*k, v))
    }

    /// Returns a DisplayDef for the given def_id
    pub fn describe_def(&self, def_id: DefId) -> DisplayDef {
        DisplayDef { ctx: self, def_id }
    }

    #[deprecated = "Use NodeExt::describe instead"]
    /// Returns a DisplayNode for the given Node
    pub fn describe_node(&self, node: GlobalNode) -> DisplayNode {
        node.describe(self)
    }

    /// Return which data is being read from for the modification performed at
    /// this location
    pub fn inputs_of(&self, call_string: CallString) -> NodeCluster {
        let ctrl_id = call_string.root().function;
        NodeCluster::new(
            ctrl_id,
            self.desc.controllers[&ctrl_id]
                .graph
                .edge_references()
                .filter(|e| e.weight().at == call_string)
                .map(|e| e.source()),
        )
    }

    /// Return which data is being written to at this location
    pub fn outputs_of(&self, call_string: CallString) -> NodeCluster {
        let ctrl_id = call_string.root().function;
        NodeCluster::new(
            ctrl_id,
            self.desc.controllers[&ctrl_id]
                .graph
                .edge_references()
                .filter(|e| e.weight().at == call_string)
                .map(|e| e.target()),
        )
    }

    #[deprecated = "Use NodeExt::info instead"]
    /// Retrieve metadata about a node.
    pub fn node_info(&self, node: GlobalNode) -> &NodeInfo {
        node.info(self)
    }

    /// Retrieve metadata about the instruction executed by a specific node.
    pub fn instruction_at_node(&self, node: GlobalNode) -> &InstructionInfo {
        node.instruction(self)
    }

    #[deprecated = "Use NodeExt::successors instead"]
    /// Return the immediate successors of this node
    pub fn successors(&self, node: GlobalNode) -> impl Iterator<Item = GlobalNode> + '_ {
        node.successors(self)
    }

    #[deprecated = "Use NodeExt::predecessors instead"]
    /// Return the immediate predecessors of this node
    pub fn predecessors(&self, node: GlobalNode) -> impl Iterator<Item = GlobalNode> + '_ {
        node.predecessors(self)
    }

    #[cfg(test)]
    pub fn nth_successors(
        &self,
        n: usize,
        src: impl IntoIterGlobalNodes + Sized,
    ) -> paralegal_spdg::NodeCluster {
        let mut start: Vec<_> = src.iter_nodes().collect();
        let ctrl = &self.desc.controllers[&src.controller_id()].graph;

        for _ in 0..n {
            start = start.into_iter().flat_map(|n| ctrl.neighbors(n)).collect();
        }
        NodeCluster::new(src.controller_id(), start)
    }

    #[deprecated = "Use NodeExt::get_location instead"]
    /// Get the span of a node
    pub fn get_location(&self, node: GlobalNode) -> &Span {
        node.get_location(self)
    }

    #[doc(hidden)]
    pub fn write_analyzed_code(
        &self,
        mut out: impl Write,
        include_signatures: bool,
        include_elided_code: bool,
    ) -> std::io::Result<()> {
        let ordered_span_set = self
            .desc
            .analyzed_spans
            .values()
            .filter(|(_, h)| include_elided_code || matches!(h, FunctionHandling::PDG))
            .map(|v| &v.0)
            .zip(std::iter::repeat(true))
            .chain(
                include_signatures
                    .then(|| {
                        self.desc
                            .def_info
                            .iter()
                            .filter(|(did, _)| self.desc.analyzed_spans.contains_key(did))
                            .map(|(_, i)| (&i.src_info, matches!(i.kind, DefKind::Type)))
                    })
                    .into_iter()
                    .flatten(),
            )
            .collect::<BTreeMap<_, _>>();
        let mut current_file = None;
        for (s, is_complete) in ordered_span_set {
            if Some(&s.source_file.file_path) != current_file {
                writeln!(out, "// {}", s.source_file.file_path)?;
                current_file = Some(&s.source_file.file_path);
            }
            let file = BufReader::new(File::open(&s.source_file.abs_file_path).unwrap());
            for l in file
                .lines()
                .skip(s.start.line as usize - 1)
                .take((s.end.line - s.start.line + 1) as usize)
            {
                writeln!(out, "{}", l.unwrap()).unwrap()
            }
            if !is_complete {
                writeln!(out, "unreachable!() }}")?;
            }
        }

        Ok(())
    }
}

/// Actions that behave differently depending on the context
pub trait Context {
    /// Get the root context object
    fn root(&self) -> &RootContext;

    /// Returns an iterator over all objects marked with `marker`.
    fn marked_nodes(&self, marker: Marker) -> impl Iterator<Item = GlobalNode> + '_;

    /// All nodes with this marker, be that via type or directly
    fn nodes_marked_any_way(&self, marker: Marker) -> impl Iterator<Item = GlobalNode> + '_;
    /// All nodes that have this marker through a type
    fn nodes_marked_via_type(&self, marker: Marker) -> impl Iterator<Item = GlobalNode> + '_;
}

impl Context for RootContext {
    fn root(&self) -> &RootContext {
        self
    }

    fn nodes_marked_any_way(&self, marker: Marker) -> impl Iterator<Item = GlobalNode> + '_ {
        self.marked_nodes(marker)
            .chain(self.nodes_marked_via_type(marker))
    }

    fn nodes_marked_via_type(&self, marker: Marker) -> impl Iterator<Item = GlobalNode> + '_ {
        self.marked_type(marker).iter().copied().flat_map(|t| {
            self.all_controllers().flat_map(move |(cid, c)| {
                c.type_assigns
                    .iter()
                    .filter(move |(_, tys)| tys.0.contains(&t))
                    .map(move |(n, _)| GlobalNode::from_local_node(cid, *n))
            })
        })
    }

    fn marked_nodes(&self, marker: Marker) -> impl Iterator<Item = GlobalNode> + '_ {
        self.report_marker_if_absent(marker);
        self.marker_to_ids
            .get(&marker)
            .into_iter()
            .flat_map(|t| &t.nodes)
            .copied()
    }
}

/// Context queries conveniently accessible on nodes
pub trait NodeQueries<'a>: IntoIterGlobalNodes
where
    Self::Iter: 'a,
{
    /// Get other nodes at the same instruction
    fn siblings(self, ctx: &RootContext) -> NodeCluster {
        NodeCluster::new(
            self.controller_id(),
            self.iter_global_nodes()
                .flat_map(|node| {
                    let self_at = node.info(ctx).at;
                    node.predecessors(ctx)
                        .flat_map(|n| n.successors(ctx))
                        .chain(node.successors(ctx).flat_map(|n| n.predecessors(ctx)))
                        .filter(move |n| n.info(ctx).at == self_at)
                        .filter(move |n| *n != node)
                        .map(|n| n.local_node())
                })
                .collect::<HashSet<_>>(),
        )
    }

    /// Returns whether a node flows to a node through the configured edge type.
    ///
    /// Nodes do not flow to themselves. CallArgument nodes do flow to their respective CallSites.
    ///
    /// If you use flows_to with [`EdgeSelection::Control`], you might want to consider using [`Context::has_ctrl_influence`], which additionally considers intermediate nodes which the src node has data flow to and has ctrl influence on the sink.
    fn flows_to(
        self,
        sink: impl IntoIterGlobalNodes,
        ctx: &RootContext,
        edge_type: EdgeSelection,
    ) -> bool {
        let cf_id = self.controller_id();
        if sink.controller_id() != cf_id {
            return false;
        }

        if let Some(index) = ctx.flows_to.as_ref() {
            if edge_type.is_data() {
                let flows_to = &index[&cf_id];
                return self.iter_nodes().any(|src| {
                    sink.iter_nodes()
                        .any(|sink| flows_to.data_flows_to[src.index()][sink.index()])
                });
            }
        }
        generic_flows_to(
            self.iter_nodes(),
            edge_type,
            &ctx.desc.controllers[&cf_id],
            sink.iter_nodes(),
        )
        .is_some()
    }

    /// Returns the sink node that is reached
    ///
    /// Nodes do not flow to themselves. CallArgument nodes do flow to their respective CallSites.
    ///
    /// If you use flows_to with [`EdgeSelection::Control`], you might want to consider using [`Context::has_ctrl_influence`], which additionally considers intermediate nodes which the src node has data flow to and has ctrl influence on the sink.
    fn find_flow(
        self,
        sink: impl IntoIterGlobalNodes,
        ctx: &RootContext,
        edge_type: EdgeSelection,
    ) -> Option<GlobalNode> {
        let cf_id = self.controller_id();
        if sink.controller_id() != cf_id {
            return None;
        }

        if let Some(index) = ctx.flows_to.as_ref() {
            if edge_type.is_data() {
                let flows_to = &index[&cf_id];
                return self.iter_nodes().find_map(|src| {
                    sink.iter_nodes()
                        .find(|sink| flows_to.data_flows_to[src.index()][sink.index()])
                        .map(|n| GlobalNode::from_local_node(cf_id, n))
                });
            }
        }
        generic_flows_to(
            self.iter_nodes(),
            edge_type,
            &ctx.desc.controllers[&cf_id],
            sink.iter_nodes(),
        )
        .map(|n| GlobalNode::from_local_node(cf_id, n))
    }

    /// Call sites that consume this node directly. E.g. the outgoing edges.
    fn consuming_call_sites(
        self,
        ctx: &'a RootContext,
    ) -> Box<dyn Iterator<Item = CallString> + 'a> {
        let ctrl = &ctx.desc.controllers[&self.controller_id()];

        Box::new(self.iter_nodes().flat_map(move |local| {
            ctrl.graph
                .edges_directed(local, Direction::Outgoing)
                .map(|e| e.weight().at)
        }))
    }

    /// Returns whether there is direct control flow influence from influencer to sink, or there is some node which is data-flow influenced by `influencer` and has direct control flow influence on `target`. Or as expressed in code:
    ///
    /// `some n where self.flows_to(influencer, n, EdgeSelection::Data) && self.flows_to(n, target, EdgeSelection::Control)`.
    fn has_ctrl_influence(
        self,
        target: impl IntoIterGlobalNodes + Sized + Copy,
        ctx: &RootContext,
    ) -> bool {
        self.flows_to(target, ctx, EdgeSelection::Control)
            || NodeCluster::try_from_iter(self.influencees(ctx, EdgeSelection::Data))
                .unwrap()
                .flows_to(target, ctx, EdgeSelection::Control)
    }

    /// Returns iterator over all Nodes that influence the given sink Node.
    ///
    /// Does not return the input node. A CallSite sink will return all of the associated CallArgument nodes.
    fn influencers(self, ctx: &RootContext, edge_type: EdgeSelection) -> Vec<GlobalNode> {
        let cf_id = self.controller_id();
        let nodes = self.iter_nodes();
        generic_influencers(&ctx.desc.controllers[&cf_id].graph, nodes, edge_type)
            .into_iter()
            .map(|n| GlobalNode::from_local_node(cf_id, n))
            .collect()
    }

    /// Returns iterator over all Nodes that are influenced by the given src Node.
    ///
    /// Does not return the input node. A CallArgument src will return the associated CallSite.
    fn influencees(self, ctx: &RootContext, edge_type: EdgeSelection) -> Vec<GlobalNode> {
        let cf_id = self.controller_id();

        let graph = &ctx.desc.controllers[&cf_id].graph;

        if let Some(index) = ctx.flows_to.as_ref() {
            if edge_type == EdgeSelection::Data {
                return self
                    .iter_nodes()
                    .flat_map(|src| {
                        index[&cf_id].data_flows_to[src.index()]
                            .iter_ones()
                            .map(move |i| GlobalNode::unsafe_new(cf_id, i))
                    })
                    .collect::<Vec<_>>();
            }
        }
        generic_influencees(graph, self.iter_nodes(), edge_type)
            .into_iter()
            .map(move |n| GlobalNode::from_local_node(cf_id, n))
            .collect()
    }
}

impl<'a, T: IntoIterGlobalNodes + 'a> NodeQueries<'a> for T {}

mod private {
    pub trait Sealed {}

    impl Sealed for super::GlobalNode {}
}

/// Extension trait with queries for single nodes
pub trait NodeExt: private::Sealed {
    /// Returns true if this node has the provided type
    fn has_type(self, t: TypeId, ctx: &RootContext) -> bool;
    /// Find the call string for the statement or function that produced this node.
    fn associated_call_site(self, ctx: &RootContext) -> CallString;
    /// Get the type(s) of a Node.
    fn types(self, ctx: &RootContext) -> &[TypeId];
    /// Returns a DisplayNode for the given Node
    fn describe(self, ctx: &RootContext) -> DisplayNode;
    /// Retrieve metadata about a node.
    fn info(self, ctx: &RootContext) -> &NodeInfo;
    /// Retrieve metadata about the instruction executed by a specific node.
    fn instruction(self, ctx: &RootContext) -> &InstructionInfo;
    /// Return the immediate successors of this node
    fn successors(self, ctx: &RootContext) -> Box<dyn Iterator<Item = GlobalNode> + '_>;
    /// Return the immediate predecessors of this node
    fn predecessors(self, ctx: &RootContext) -> Box<dyn Iterator<Item = GlobalNode> + '_>;
    /// Get the span of a node
    fn get_location(self, ctx: &RootContext) -> &Span;
    /// Returns whether this Node has the marker applied to it directly or via its type.
    fn has_marker<C: HasDiagnosticsBase>(self, ctx: C, marker: Marker) -> bool;
    /// The shortest path between this and a target node
    #[deprecated = "This function is known to be buggy at the moment. Only use for debugging, don't rely on it for policy correctness."]
    fn shortest_path(
        self,
        to: GlobalNode,
        ctx: &RootContext,
        edge_selection: EdgeSelection,
    ) -> Option<Box<[GlobalNode]>>;
}

impl NodeExt for GlobalNode {
    fn has_type(self, t: TypeId, ctx: &RootContext) -> bool {
        ctx.desc().controllers[&self.controller_id()]
            .type_assigns
            .get(&self.local_node())
            .map_or(false, |tys| tys.0.contains(&t))
    }
    fn associated_call_site(self, ctx: &RootContext) -> CallString {
        ctx.desc.controllers[&self.controller_id()]
            .node_info(self.local_node())
            .at
    }

    fn types(self, ctx: &RootContext) -> &[TypeId] {
        ctx.desc.controllers[&self.controller_id()]
            .type_assigns
            .get(&self.local_node())
            .map_or(&[], |v| v.0.as_ref())
    }

    fn describe(self, ctx: &RootContext) -> DisplayNode {
        DisplayNode::pretty(
            self.local_node(),
            &ctx.desc.controllers[&self.controller_id()],
        )
    }

    fn info(self, ctx: &RootContext) -> &NodeInfo {
        ctx.desc.controllers[&self.controller_id()].node_info(self.local_node())
    }

    fn instruction(self, ctx: &RootContext) -> &InstructionInfo {
        &ctx.desc.instruction_info[&self.info(ctx).at.leaf()]
    }

    fn successors(self, ctx: &RootContext) -> Box<dyn Iterator<Item = GlobalNode> + '_> {
        Box::new(
            ctx.desc.controllers[&self.controller_id()]
                .graph
                .neighbors(self.local_node())
                .map(move |n| GlobalNode::from_local_node(self.controller_id(), n)),
        )
    }

    fn predecessors(self, ctx: &RootContext) -> Box<dyn Iterator<Item = GlobalNode> + '_> {
        Box::new(
            ctx.desc.controllers[&self.controller_id()]
                .graph
                .neighbors_directed(self.local_node(), petgraph::Direction::Incoming)
                .map(move |n| GlobalNode::from_local_node(self.controller_id(), n)),
        )
    }
    fn get_location(self, ctx: &RootContext) -> &Span {
        &self.info(ctx).span
    }

    /// Returns whether this Node has the marker applied to it directly or via its type.
    fn has_marker<C: HasDiagnosticsBase>(self, ctx: C, marker: Marker) -> bool {
        let Some(marked) = ctx.as_ctx().marker_to_ids.get(&marker) else {
            ctx.warning(format!("No marker named '{marker}' known"));
            return false;
        };
        marked.nodes.contains(&self)
            || self
                .types(ctx.as_ctx())
                .iter()
                .any(|t| marked.types.contains(t))
    }

    fn shortest_path(
        self,
        to: Self,
        ctx: &RootContext,
        edge_selection: EdgeSelection,
    ) -> Option<Box<[Self]>> {
        let g = if self.controller_id() != to.controller_id() {
            return None;
        } else {
            &ctx.desc.controllers[&self.controller_id()]
        };
        let mut ancestors = HashMap::new();
        let filtered = edge_selection.filter_graph(&g.graph);
        let fg = Reversed(&filtered);
        let mut found = false;
        'outer: for this in petgraph::visit::Bfs::new(&fg, self.local_node()).iter(&fg) {
            for next in fg.neighbors_directed(this, Outgoing) {
                if next != this {
                    ancestors.entry(next).or_insert(this);
                }
                if next == to.local_node() {
                    found = true;
                    break 'outer;
                }
            }
        }
        found.then(|| {
            std::iter::successors(Some(to.local_node()), |elem| {
                let n = ancestors.get(elem).copied()?;
                (n != self.local_node()).then_some(n)
            })
            .map(|n| GlobalNode::from_local_node(self.controller_id(), n))
            .collect()
        })
    }
}

impl<T: Sealed> Sealed for &'_ T {}

impl<T: NodeExt + Copy> NodeExt for &'_ T {
    fn has_type(self, t: TypeId, ctx: &RootContext) -> bool {
        (*self).has_type(t, ctx)
    }
    fn info(self, ctx: &RootContext) -> &NodeInfo {
        (*self).info(ctx)
    }

    fn types(self, ctx: &RootContext) -> &[TypeId] {
        (*self).types(ctx)
    }

    fn describe(self, ctx: &RootContext) -> DisplayNode {
        (*self).describe(ctx)
    }

    fn has_marker<C: HasDiagnosticsBase>(self, ctx: C, marker: Marker) -> bool {
        (*self).has_marker(ctx, marker)
    }

    fn successors(self, ctx: &RootContext) -> Box<dyn Iterator<Item = GlobalNode> + '_> {
        (*self).successors(ctx)
    }

    fn instruction(self, ctx: &RootContext) -> &InstructionInfo {
        (*self).instruction(ctx)
    }

    fn get_location(self, ctx: &RootContext) -> &Span {
        (*self).get_location(ctx)
    }

    fn predecessors(self, ctx: &RootContext) -> Box<dyn Iterator<Item = GlobalNode> + '_> {
        (*self).predecessors(ctx)
    }

    fn shortest_path(
        self,
        to: GlobalNode,
        ctx: &RootContext,
        edge_selection: EdgeSelection,
    ) -> Option<Box<[GlobalNode]>> {
        (*self).shortest_path(to, ctx, edge_selection)
    }

    fn associated_call_site(self, ctx: &RootContext) -> CallString {
        (*self).associated_call_site(ctx)
    }
}

/// Provide display trait for DefId in a Context.
pub struct DisplayDef<'a> {
    /// DefId to display.
    pub def_id: DefId,
    /// Context for the DefId.
    pub ctx: &'a RootContext,
}

impl<'a> std::fmt::Display for DisplayDef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Write;
        let info = &self.ctx.desc().def_info[&self.def_id];
        f.write_str(info.kind.as_ref())?;
        f.write_str(" `")?;
        for segment in info.path.as_ref() {
            f.write_str(segment.as_str())?;
            f.write_str("::")?;
        }
        f.write_str(info.name.as_str())?;
        f.write_char('`')
    }
}

#[cfg(test)]
fn overlaps<T: Eq + std::hash::Hash>(
    one: impl IntoIterator<Item = T>,
    other: impl IntoIterator<Item = T>,
) -> bool {
    let target = one.into_iter().collect::<HashSet<_>>();
    other.into_iter().any(|n| target.contains(&n))
}

#[test]
#[ignore = "This does a lof of counting of marked nodes, which I'm not sure is the right way to test this behavior at the moment."]
fn test_context() {
    let ctx = crate::test_utils::test_ctx();
    assert!(ctx
        .marked_type(Marker::new_intern("input"))
        .iter()
        .any(|id| ctx
            .desc
            .def_info
            .get(id)
            .map_or(false, |info| info.name.as_str().starts_with("Foo"))));

    let controller = ctx
        .controller_by_name(Identifier::new_intern("controller"))
        .unwrap();

    // The two Foo inputs are marked as input via the type, input and output of identity also marked via the type
    assert_eq!(
        ctx.all_nodes_for_ctrl(controller)
            .filter(|n| n.has_marker(&ctx, Marker::new_intern("input")))
            .count(),
        3
    );
    let src_markers = ctx
        .all_nodes_for_ctrl(controller)
        .filter(|n| n.has_marker(&ctx, Marker::new_intern("src")))
        .collect::<Vec<_>>();
    // Return of identity marked as src
    assert_eq!(src_markers.len(), 1);
    // The sinks are marked via arguments
    assert_eq!(
        ctx.all_nodes_for_ctrl(controller)
            .filter(|n| n.has_marker(&ctx, Marker::new_intern("sink")))
            .count(),
        3
    );
    // The 3rd argument and the return of the controller.
    assert_eq!(
        ctx.all_nodes_for_ctrl(controller)
            .filter(|n| n.has_marker(&ctx, Marker::new_intern("ctrl")))
            .count(),
        2
    );
}

#[test]
fn test_influencees() -> Result<()> {
    let ctx = crate::test_utils::test_ctx();
    let ctrl_name = ctx.controller_by_name(Identifier::new_intern("influence"))?;
    let src_a = ctx.controller_argument(ctrl_name, 0).unwrap();
    let cond_sink = crate::test_utils::get_sink_node(&ctx, ctrl_name, "cond");
    let sink_callsite = crate::test_utils::get_callsite_node(&ctx, ctrl_name, "sink1");

    let influencees_data_control = ctx
        .influencees(dbg!(src_a), EdgeSelection::Both)
        .unique()
        .collect::<Vec<_>>();
    let influencees_data = ctx
        .influencees(src_a, EdgeSelection::Data)
        .unique()
        .collect::<Vec<_>>();

    assert!(
        overlaps(
            influencees_data_control.iter().copied(),
            cond_sink.iter_global_nodes()
        ),
        "input argument a influences cond via data"
    );
    assert!(
        overlaps(
            influencees_data_control.iter().copied(),
            sink_callsite.iter_global_nodes()
        ),
        "input argument a influences sink via control"
    );

    assert!(
        overlaps(
            influencees_data.iter().copied(),
            cond_sink.iter_global_nodes()
        ),
        "input argument a influences cond via data"
    );
    assert!(
        !overlaps(
            influencees_data.iter().copied(),
            sink_callsite.iter_global_nodes()
        ),
        "input argument a doesnt influence sink via data"
    );

    Ok(())
}

#[test]
fn test_influencers() -> Result<()> {
    let ctx = crate::test_utils::test_ctx();
    let ctrl_name = ctx.controller_by_name(Identifier::new_intern("influence"))?;
    let src_a = ctx.controller_argument(ctrl_name, 0).unwrap();
    let src_b = ctx.controller_argument(ctrl_name, 1).unwrap();
    let cond_sink = crate::test_utils::get_sink_node(&ctx, ctrl_name, "cond");
    let sink_callsite = crate::test_utils::get_callsite_node(&ctx, ctrl_name, "sink1");

    let influencers_data_control = ctx
        .influencers(dbg!(&sink_callsite), EdgeSelection::Both)
        .unique()
        .collect::<Vec<_>>();
    let influencers_data = ctx
        .influencers(&sink_callsite, EdgeSelection::Data)
        .unique()
        .collect::<Vec<_>>();

    assert!(
        influencers_data_control.contains(&src_a),
        "input argument a influences sink via data"
    );
    assert!(
        influencers_data_control.contains(&dbg!(src_b)),
        "input argument b influences sink via control"
    );
    assert!(
        overlaps(
            influencers_data_control.iter().copied(),
            dbg!(&cond_sink).iter_global_nodes()
        ),
        "cond_sink influences sink via control"
    );

    assert!(
        !influencers_data.contains(&src_a),
        "input argument a doesnt influences sink via data"
    );
    assert!(
        influencers_data.contains(&src_b),
        "input argument b influences sink via data"
    );
    assert!(
        !overlaps(
            influencers_data.iter().copied(),
            cond_sink.iter_global_nodes()
        ),
        "cond_sink doesnt influence sink via data"
    );

    Ok(())
}

#[test]
#[ignore = "Something is weird with the PDG construction here.
    See https://github.com/willcrichton/flowistry/issues/95"]
fn test_has_ctrl_influence() -> Result<()> {
    let ctx = crate::test_utils::test_ctx();
    let ctrl_name = ctx.controller_by_name(Identifier::new_intern("ctrl_influence"))?;
    let src_a = ctx.controller_argument(ctrl_name, 0).unwrap();
    let src_b = ctx.controller_argument(ctrl_name, 1).unwrap();
    let a_identity = crate::test_utils::get_callsite_or_datasink_node(&ctx, ctrl_name, "identity");
    let b_identity = crate::test_utils::get_callsite_or_datasink_node(&ctx, ctrl_name, "id");
    let validate =
        crate::test_utils::get_callsite_or_datasink_node(&ctx, ctrl_name, "validate_foo");
    let sink_cs = crate::test_utils::get_callsite_or_datasink_node(&ctx, ctrl_name, "sink1");

    assert!(
        ctx.has_ctrl_influence(src_a, &sink_cs),
        "src_a influences sink"
    );
    assert!(
        ctx.has_ctrl_influence(&dbg!(a_identity), dbg!(&sink_cs)),
        "a_prime influences sink"
    );
    assert!(
        ctx.has_ctrl_influence(&validate, &sink_cs),
        "validate_foo influences sink"
    );
    assert!(
        !ctx.has_ctrl_influence(src_b, &sink_cs),
        "src_b doesnt influence sink"
    );
    assert!(
        !ctx.has_ctrl_influence(&b_identity, &sink_cs),
        "b_prime doesnt influence sink"
    );

    Ok(())
}
