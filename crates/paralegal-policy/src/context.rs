use std::{io::Write, process::exit, sync::Arc};

pub use paralegal_spdg::rustc_portable::{DefId, LocalDefId};
use paralegal_spdg::{CallString, Endpoint, HashMap, Identifier, Node as SPDGNode, ProgramDescription, SPDGImpl, TypeId, SPDG, GlobalNode};

use anyhow::{anyhow, bail, ensure, Result};
use itertools::{Either, Itertools};
use petgraph::prelude::Bfs;
use petgraph::visit::{Control, DfsEvent, EdgeFiltered, EdgeRef, Walker};
use petgraph::Incoming;

use super::flows_to::CtrlFlowsTo;

use crate::{
    assert_error, assert_warning,
    diagnostics::{CombinatorContext, DiagnosticsRecorder, HasDiagnosticsBase},
    flows_to::DataAndControlInfluencees,
};

/// User-defined PDG markers.
pub type Marker = Identifier;

/// The type identifying a controller
pub type ControllerId = LocalDefId;
/// The type identifying a function that is used in call sites.
pub type FunctionId = DefId;

/// Identifier for a graph element that allows attaching a marker.
pub type MarkableId = GlobalNode;

type MarkerIndex = HashMap<Marker, MarkerTargets>;
type FlowsTo = HashMap<ControllerId, CtrlFlowsTo>;

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

/// Enum for identifying an edge type (data, control or both)
#[derive(Clone, Copy)]
pub enum EdgeType {
    /// Only consider dataflow edges
    Data,
    /// Only consider control flow edges
    Control,
    /// Consider both types of edges
    DataAndControl,
}

impl GlobalNode {
    /// Transform a Node into the associated Node with typ [`NodeType::CallSite`]
}

use petgraph::visit::{GraphRef, IntoNeighbors, Visitable};

fn bfs_iter<
    G: IntoNeighbors + GraphRef + Visitable<NodeId = SPDGNode, Map = <SPDGImpl as Visitable>::Map>,
>(
    g: G,
    start: GlobalNode,
) -> impl Iterator<Item =GlobalNode> {
    let walker_iter = Walker::iter(Bfs::new(g, start.inner), g);
    walker_iter.map(move |inner| GlobalNode {
        ctrl_id: start.ctrl_id,
        inner,
    })
}

/// Interface for defining policies.
///
/// Holds a PDG ([`Self::desc`]) and defines basic queries like
/// [`Self::all_nodes_for_ctrl`] and combinators such as
/// [`Self::always_happens_before`]. These should be composed into more complex
/// policies.
///
/// To communicate the results of your policies with the user you can emit
/// diagnostic messages. To communicate a policy failure use
/// [`error`](crate::Diagnostics::error) or the [`assert_error`] macro. To
/// communicate suspicious circumstances that are not outright cause for failure
/// use [`warning`](crate::Diagnostics::error) or [`assert_warning`].
///
/// Note that these methods just queue the diagnostics messages. To emit them
/// (and potentially terminate the program if the policy does not hold) use
/// [`Self::emit_diagnostics`]. If you used
/// [`super::GraphLocation::with_context`] this will be done automatically for
/// you.
#[derive(Debug)]
pub struct Context {
    marker_to_ids: MarkerIndex,
    desc: ProgramDescription,
    flows_to: FlowsTo,
    pub(crate) diagnostics: DiagnosticsRecorder,
    name_map: HashMap<Identifier, Vec<DefId>>,
}

impl Context {
    /// Construct a [`Context`] from a [`ProgramDescription`].
    ///
    /// This also precomputes some data structures like an index over markers.
    pub fn new(desc: ProgramDescription) -> Self {
        let name_map = desc
            .def_info
            .iter()
            .map(|(k, v)| (v.name, *k))
            .into_group_map();
        Context {
            marker_to_ids: Self::build_index_on_markers(&desc),
            flows_to: Self::build_flows_to(&desc),
            desc,
            diagnostics: Default::default(),
            name_map,
        }
    }

    pub fn associated_call_site(&self, node: GlobalNode) -> CallString {
        self.desc.controllers[&node.controller_id()]
            .node_info(node.local_node())
            .at
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
            .iter()
            .flat_map(|(&ctrl_id, spdg)| {
                spdg.markers.iter().flat_map(move |(&inner, anns)| {
                    anns.iter()
                        .map(move |marker| (*marker, Either::Left(GlobalNode { inner, ctrl_id })))
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

    /// Returns whether a node flows to a node through the configured edge type.
    ///
    /// Nodes do not flow to themselves. CallArgument nodes do flow to their respective CallSites.
    ///
    /// If you use flows_to with [`EdgeType::Control`], you might want to consider using [`Context::has_ctrl_influence`], which additionally considers intermediate nodes which the src node has data flow to and has ctrl influence on the sink.
    pub fn flows_to(&self, src: GlobalNode, sink: GlobalNode, edge_type: EdgeType) -> bool {
        if src.ctrl_id != sink.ctrl_id {
            return false;
        }

        let cf_id = &src.ctrl_id;
        let src_datasource = src.inner;
        let sink_cs_or_ds = sink.inner;

        match edge_type {
            EdgeType::Data => {
                self.flows_to[cf_id].data_flows_to[src_datasource.index()][sink_cs_or_ds.index()]
            }
            EdgeType::DataAndControl => {
                DataAndControlInfluencees::new(src_datasource, &self.desc.controllers[cf_id])
                    .contains(&sink_cs_or_ds)
            }
            EdgeType::Control => self
                .desc
                .controllers
                .get(cf_id)
                .unwrap()
                .graph
                .edges(src_datasource)
                .any(|e| e.weight().is_control() && e.target() == sink_cs_or_ds),
        }
    }

    /// Find the node that represents the `index`th argument of the controller
    /// `ctrl_id`.
    ///
    /// ### Returns `None`
    ///
    /// If the controller with this id does not exist *or* the controller has
    /// fewer than `index` arguments.
    pub fn controller_argument(&self, ctrl_id: ControllerId, index: u32) -> Option<GlobalNode> {
        let ctrl = self.desc.controllers.get(&ctrl_id)?;
        let inner = *ctrl.arguments.get(index as usize)?;

        Some(GlobalNode { ctrl_id, inner })
    }

    /// Returns whether there is direct control flow influence from influencer to sink, or there is some node which is data-flow influenced by `influencer` and has direct control flow influence on `target`. Or as expressed in code:
    ///
    /// `some n where self.flows_to(influencer, n, EdgeType::Data) && self.flows_to(n, target, Edgetype::Control)`.
    pub fn has_ctrl_influence(&self, influencer: GlobalNode, target: GlobalNode) -> bool {
        self.flows_to(influencer, target, EdgeType::Control)
            || self
                .influencees(influencer, EdgeType::Data)
                .any(|inf| self.flows_to(inf, target, EdgeType::Control))
    }

    /// Returns iterator over all Nodes that influence the given sink Node.
    ///
    /// Does not return the input node. A CallSite sink will return all of the associated CallArgument nodes.
    pub fn influencers<'a>(
        &'a self,
        sink: GlobalNode,
        edge_type: EdgeType,
    ) -> Box<dyn Iterator<Item =GlobalNode> + 'a> {
        use petgraph::visit::*;
        let cf_id = &sink.ctrl_id;

        let reversed_graph = Reversed(&self.desc.controllers[cf_id].graph);

        match edge_type {
            EdgeType::Data => {
                let edges_filtered =
                    EdgeFiltered::from_fn(reversed_graph, |e| e.weight().is_data());
                Box::new(
                    // TODO: Yikes. Can't create a lazy iterator from
                    // `edges_filtered` because they must be taken by
                    // reference by `Walker::iter`
                    bfs_iter(&edges_filtered, sink)
                        .collect::<Vec<_>>()
                        .into_iter(),
                ) as Box<dyn Iterator<Item =GlobalNode> + 'a>
            }
            EdgeType::Control => {
                let edges_filtered =
                    EdgeFiltered::from_fn(reversed_graph, |e| e.weight().is_control());
                Box::new(
                    // TODO: Yikes. Can't create a lazy iterator from
                    // `edges_filtered` because they must be taken by
                    // reference by `Walker::iter`
                    bfs_iter(&edges_filtered, sink)
                        .collect::<Vec<_>>()
                        .into_iter(),
                ) as Box<_>
            }
            EdgeType::DataAndControl => Box::new(bfs_iter(reversed_graph, sink)) as Box<_>,
        }
    }

    /// Returns iterator over all Nodes that are influenced by the given src Node.
    ///
    /// Does not return the input node. A CallArgument src will return the associated CallSite.
    pub fn influencees<'a>(
        &'a self,
        src: GlobalNode,
        edge_type: EdgeType,
    ) -> Box<dyn Iterator<Item =GlobalNode> + 'a> {
        let cf_id = &src.ctrl_id;
        let src_ctrl_id = src.ctrl_id;

        let graph = &self.desc.controllers[cf_id].graph;

        match edge_type {
            EdgeType::Data => Box::new(
                self.flows_to[&cf_id].data_flows_to[src.inner.index()]
                    .iter_ones()
                    .map(move |i| GlobalNode::unsafe_new(src_ctrl_id, i)),
            ) as Box<dyn Iterator<Item =GlobalNode> + 'a>,
            EdgeType::DataAndControl => Box::new(bfs_iter(graph, src)) as Box<_>,
            EdgeType::Control => {
                let edges_filtered = EdgeFiltered::from_fn(graph, |e| e.weight().is_control());
                Box::new(
                    bfs_iter(&edges_filtered, src)
                        // TODO: Yikes. Can't create a lazy iterator from
                        // `edges_filtered` because they must be taken by
                        // reference by `Walker::iter`
                        .collect::<Vec<_>>()
                        .into_iter(),
                ) as Box<_>
            }
        }
    }

    /// Returns an iterator over all objects marked with `marker`.
    pub fn marked_nodes(&self, marker: Marker) -> impl Iterator<Item =GlobalNode> + '_ {
        self.report_marker_if_absent(marker);
        self.marker_to_ids
            .get(&marker)
            .into_iter()
            .flat_map(|t| &t.nodes)
            .copied()
    }

    /// Get the type(s) of a Node.
    pub fn get_node_types(&self, node: GlobalNode) -> &[DefId] {
        self.desc.controllers[&node.ctrl_id]
            .types
            .get(&node.inner)
            .map_or(&[], |v| v.0.as_slice())
    }

    /// Returns whether the given Node has the marker applied to it directly or via its type.
    pub fn has_marker(&self, marker: Marker, node: GlobalNode) -> bool {
        let types = self.get_node_types(node);
        if types.iter().any(|_t| {
            self.marker_to_ids
                .get(&marker)
                .map(|markers| markers.nodes.contains(&node))
                .unwrap_or(false)
        }) {
            return true;
        }

        self.desc.controllers[&node.ctrl_id].markers[&node.inner]
            .iter()
            .any(|ann| *ann == marker)
    }

    /// Returns all DataSources, DataSinks, and CallSites for a Controller as Nodes.
    pub fn all_nodes_for_ctrl(&self, ctrl_id: ControllerId) -> impl Iterator<Item =GlobalNode> + '_ {
        let ctrl = &self.desc.controllers[&ctrl_id];
        ctrl.graph
            .node_indices()
            .map(move |inner| GlobalNode { ctrl_id, inner })
    }

    /// Returns an iterator over the data sources within controller `c` that have type `t`.
    pub fn srcs_with_type(
        &self,
        ctrl_id: ControllerId,
        t: DefId,
    ) -> impl Iterator<Item =GlobalNode> + '_ {
        self.desc.controllers[&ctrl_id]
            .types
            .iter()
            .filter_map(move |(src, ids)| {
                ids.0.contains(&t).then_some(GlobalNode {
                    ctrl_id,
                    inner: *src,
                })
            })
    }

    /// Returns an iterator over all nodes that do not have any influencers of the given edge_type.
    pub fn roots(
        &self,
        ctrl_id: ControllerId,
        _edge_type: EdgeType,
    ) -> impl Iterator<Item =GlobalNode> + '_ {
        let g = &self.desc.controllers[&ctrl_id].graph;
        g.externals(Incoming)
            .map(move |inner| GlobalNode { ctrl_id, inner })
    }

    /// Returns the input [`ProgramDescription`].
    pub fn desc(&self) -> &ProgramDescription {
        &self.desc
    }

    /// Returns all the [`Annotation::OType`]s for a controller `id`.
    pub fn otypes(&self, id: DefId) -> &[DefId] {
        self.desc()
            .type_info
            .get(&id)
            .map_or(&[], |info| info.otypes.as_slice())
    }

    /// Enforce that on every data flow path from the `starting_points` to `is_terminal` a
    /// node satisfying `is_checkpoint` is passed.
    ///
    /// Fails if `ctrl_id` on a provided starting point is not found.
    ///
    /// The return value contains some statistics information about the
    /// traversal. The property holds if [`AlwaysHappensBefore::holds`] is true.
    ///
    /// Note that `is_checkpoint` and `is_terminal` will be called many times
    /// and should thus be efficient computations. In addition they should
    /// always return the same result for the same input.
    pub fn always_happens_before(
        &self,
        starting_points: impl Iterator<Item =GlobalNode>,
        mut is_checkpoint: impl FnMut(GlobalNode) -> bool,
        mut is_terminal: impl FnMut(GlobalNode) -> bool,
    ) -> Result<AlwaysHappensBefore> {
        let mut num_reached = 0;
        let mut num_checkpointed = 0;

        let start_map = starting_points
            .map(|i| (i.ctrl_id, i.inner))
            .into_group_map();
        let started_with = start_map.values().map(Vec::len).sum();

        for (ctrl_id, starts) in start_map {
            let g = &self.desc.controllers[&ctrl_id].graph;
            petgraph::visit::depth_first_search(g, starts, |event| match event {
                DfsEvent::Discover(inner, _) => {
                    let as_node = GlobalNode { ctrl_id, inner };
                    if is_checkpoint(as_node) {
                        num_checkpointed += 1;
                        Control::<()>::Prune
                    } else if is_terminal(as_node) {
                        num_reached += 1;
                        Control::Prune
                    } else {
                        Control::Continue
                    }
                }
                _ => Control::Continue,
            });
        }

        Ok(AlwaysHappensBefore {
            num_reached,
            num_checkpointed,
            started_with,
        })
    }

    // This lifetime is actually needed but clippy doesn't understand that
    #[allow(clippy::needless_lifetimes)]
    /// Return all types that are marked with `marker`
    pub fn marked_type<'a>(&'a self, marker: Marker) -> &[DefId] {
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
        edge_type: EdgeType,
    ) -> Option<(GlobalNode, GlobalNode)> {
        from.iter().find_map(|src| {
            to.iter().find_map(|sink| {
                self.flows_to(*src, *sink, edge_type)
                    .then_some((*src, *sink))
            })
        })
    }

    /// Iterate over all defined controllers
    pub fn all_controllers(&self) -> impl Iterator<Item = (ControllerId, &SPDG)> {
        self.desc().controllers.iter().map(|(k, v)| (*k, v))
    }

    /// Returns a DisplayDef for the given def_id
    pub fn describe_def(&self, def_id: DefId) -> DisplayDef {
        DisplayDef { ctx: self, def_id }
    }

    /// Returns a DisplayNode for the given Node
    pub fn describe_node(&self, node: GlobalNode) -> DisplayNode {
        DisplayNode { ctx: self, node }
    }
}

/// Provide display trait for DefId in a Context.
pub struct DisplayDef<'a> {
    /// DefId to display.
    pub def_id: DefId,
    /// Context for the DefId.
    pub ctx: &'a Context,
}

impl<'a> std::fmt::Display for DisplayDef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Write;
        let info = &self.ctx.desc().def_info[&self.def_id];
        f.write_str(info.kind.as_ref())?;
        f.write_str(" `")?;
        for segment in &info.path {
            f.write_str(segment.as_str())?;
            f.write_str("::")?;
        }
        f.write_str(info.name.as_str())?;
        f.write_char('`')
    }
}

/// Provide display trait for Node in a Context.
pub struct DisplayNode<'a> {
    /// Node to display.
    pub node: GlobalNode,
    /// Context for the Node.
    pub ctx: &'a Context,
}

impl<'a> std::fmt::Display for DisplayNode<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Controller: {:?}",
            self.ctx.desc.controllers[&self.node.ctrl_id].name
        )?;
        f.write_str("\n")?;

        let spdg = &self.ctx.desc.controllers[&self.node.ctrl_id];
        let node = self.node.inner;
        if node == spdg.return_ {
            f.write_str("Return")
        } else if let Some((idx, _)) = spdg.arguments.iter().enumerate().find(|(_, n)| **n == node)
        {
            write!(f, "ControllerArgument:{idx}")
        } else {
            let info = spdg.node_info(node);
            write!(f, "{} @ {}", info.description, info.at)
        }
    }
}

/// Statistics about the result of running [`Context::always_happens_before`]
/// that are useful to understand how the property failed.
///
/// The [`std::fmt::Display`] implementation presents the information in human
/// readable form.
///
/// Note: Both the number of seen paths and the number of violation paths are
/// approximations. This is because the traversal terminates when it reaches a
/// node that was already seen. However it is guaranteed that if there
/// are any violating paths, then the number of reaching paths reported in this
/// struct is at least one (e.g. [`Self::holds`] is sound).
///
/// The stable API of this struct is [`Self::holds`], [`Self::assert_holds`] and
/// [`Self::is_vacuous`]. Otherwise the information in this struct and its
/// printed representations should be considered unstable and
/// for-human-eyes-only.
pub struct AlwaysHappensBefore {
    /// How many paths terminated at the end?
    num_reached: i32,
    /// How many paths lead to the checkpoints?
    num_checkpointed: i32,
    /// How large was the set of initial nodes this traversal started with.
    started_with: usize,
}

impl std::fmt::Display for AlwaysHappensBefore {
    /// Format the results of this combinator, using the `def_info` to print
    /// readable names instead of ids
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            num_reached,
            num_checkpointed,
            started_with,
        } = self;
        write!(
            f,
            "{num_reached} paths reached the terminal, \
            {num_checkpointed} paths reached the checkpoints, \
            started with {started_with} nodes"
        )
    }
}

lazy_static::lazy_static! {
    static ref ALWAYS_HAPPENS_BEFORE_NAME: Identifier = Identifier::new_intern("always_happens_before");
}

impl AlwaysHappensBefore {
    /// Check this property holds and report it as diagnostics in the context.
    ///
    /// Additionally reports if the property was vacuous or had no starting
    /// nodes.
    pub fn report(&self, ctx: Arc<dyn HasDiagnosticsBase>) {
        let ctx = CombinatorContext::new(*ALWAYS_HAPPENS_BEFORE_NAME, ctx);
        assert_warning!(ctx, self.started_with != 0, "Started with 0 nodes.");
        assert_warning!(ctx, !self.is_vacuous(), "Is vacuously true.");
        assert_error!(ctx, self.holds(), format!("Violation detected: {}", self));
    }

    /// Returns `true` if the property that created these statistics holds.
    pub fn holds(&self) -> bool {
        self.num_reached == 0
    }

    /// Fails if [`Self::holds`] is false.
    pub fn assert_holds(&self) -> Result<()> {
        ensure!(
            self.holds(),
            "AlwaysHappensBefore failed: found {} violating paths",
            self.num_reached
        );
        Ok(())
    }

    /// `true` if this policy applied to no paths. E.g. either no starting nodes
    /// or no path from them can reach the terminal or the checkpoints (the
    /// graphs are disjoined).
    pub fn is_vacuous(&self) -> bool {
        self.num_checkpointed + self.num_reached == 0
    }
}

#[test]
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
            .filter(|n| ctx.has_marker(Marker::new_intern("input"), *n))
            .count(),
        4
    );
    // Return of identity marked as src
    assert_eq!(
        ctx.all_nodes_for_ctrl(controller)
            .filter(|n| ctx.has_marker(Marker::new_intern("src"), *n))
            .count(),
        1
    );
    // The sinks are marked via arguments
    assert_eq!(
        ctx.all_nodes_for_ctrl(controller)
            .filter(|n| ctx.has_marker(Marker::new_intern("sink"), *n))
            .count(),
        2
    );
    // The 3rd argument and the return of the controller.
    assert_eq!(
        ctx.all_nodes_for_ctrl(controller)
            .filter(|n| ctx.has_marker(Marker::new_intern("ctrl"), *n))
            .count(),
        2
    );
}

#[test]
fn test_happens_before() -> Result<()> {
    let ctx = crate::test_utils::test_ctx();

    let is_terminal =
        |end: GlobalNode| -> bool { ctx.desc.controllers[&end.ctrl_id].return_ == end.inner };

    let ctrl_name = ctx.controller_by_name(Identifier::new_intern("happens_before_pass"))?;
    let pass = ctx.always_happens_before(
        ctx.all_nodes_for_ctrl(ctrl_name)
            .filter(|n| ctx.has_marker(Identifier::new_intern("start"), *n)),
        |checkpoint| ctx.has_marker(Identifier::new_intern("bless"), checkpoint),
        is_terminal,
    )?;

    ensure!(pass.holds());
    ensure!(!pass.is_vacuous(), "{pass}");

    let ctrl_name = ctx.controller_by_name(Identifier::new_intern("happens_before_fail"))?;

    let fail = ctx.always_happens_before(
        ctx.all_nodes_for_ctrl(ctrl_name)
            .filter(|n| ctx.has_marker(Identifier::new_intern("start"), *n)),
        |check| ctx.has_marker(Identifier::new_intern("bless"), check),
        is_terminal,
    )?;

    ensure!(!fail.holds());
    ensure!(!fail.is_vacuous());

    Ok(())
}

#[test]
fn test_influencees() -> Result<()> {
    let ctx = crate::test_utils::test_ctx();
    let ctrl_name = ctx.controller_by_name(Identifier::new_intern("influence"))?;
    let src_a = ctx.controller_argument(ctrl_name, 0).unwrap();
    let cond_sink = crate::test_utils::get_sink_node(&ctx, ctrl_name, "cond").unwrap();
    let sink_callsite = crate::test_utils::get_callsite_node(&ctx, ctrl_name, "sink1").unwrap();

    let influencees_data_control = ctx
        .influencees(src_a, EdgeType::DataAndControl)
        .unique()
        .collect::<Vec<_>>();
    let influencees_data = ctx
        .influencees(src_a, EdgeType::Data)
        .unique()
        .collect::<Vec<_>>();

    assert!(
        influencees_data_control.contains(&cond_sink),
        "input argument a influences cond via data"
    );
    assert!(
        influencees_data_control.contains(&sink_callsite),
        "input argument a influences sink via control"
    );
    // a influences cond arg + cs, sink1 arg + cs
    assert_eq!(influencees_data_control.len(), 4);

    assert!(
        influencees_data.contains(&cond_sink),
        "input argument a influences cond via data"
    );
    assert!(
        !influencees_data.contains(&sink_callsite),
        "input argument a doesnt influence sink via data"
    );
    // a influences cond arg + cs
    assert_eq!(influencees_data.len(), 2);

    Ok(())
}

#[test]
fn test_callsite_is_arg_influencee() -> Result<()> {
    let ctx = crate::test_utils::test_ctx();
    let ctrl_name = ctx.controller_by_name(Identifier::new_intern("influence"))?;
    let sink_arg = crate::test_utils::get_sink_node(&ctx, ctrl_name, "sink1").unwrap();
    let sink_callsite = crate::test_utils::get_callsite_node(&ctx, ctrl_name, "sink1").unwrap();

    let influencees = ctx
        .influencees(sink_arg, EdgeType::Data)
        .collect::<Vec<_>>();

    assert!(
        influencees.contains(&sink_callsite),
        "arg influences callsite through data"
    );

    Ok(())
}

#[test]
fn test_influencers() -> Result<()> {
    let ctx = crate::test_utils::test_ctx();
    let ctrl_name = ctx.controller_by_name(Identifier::new_intern("influence"))?;
    let src_a = ctx.controller_argument(ctrl_name, 0).unwrap();
    let src_b = ctx.controller_argument(ctrl_name, 1).unwrap();
    let cond_sink = crate::test_utils::get_sink_node(&ctx, ctrl_name, "cond").unwrap();
    let sink_callsite = crate::test_utils::get_callsite_node(&ctx, ctrl_name, "sink1").unwrap();

    let influencers_data_control = ctx
        .influencers(sink_callsite, EdgeType::DataAndControl)
        .unique()
        .collect::<Vec<_>>();
    let influencers_data = ctx
        .influencers(sink_callsite, EdgeType::Data)
        .unique()
        .collect::<Vec<_>>();

    assert!(
        influencers_data_control.contains(&src_a),
        "input argument a influences sink via data"
    );
    assert!(
        influencers_data_control.contains(&src_b),
        "input argument b influences sink via control"
    );
    assert!(
        influencers_data_control.contains(&cond_sink),
        "cond_sink influences sink via control"
    );
    // sink is influenced by a, b, cond arg + cs, and its own arg
    assert_eq!(influencers_data_control.len(), 5);

    assert!(
        !influencers_data.contains(&src_a),
        "input argument a doesnt influences sink via data"
    );
    assert!(
        influencers_data.contains(&src_b),
        "input argument b influences sink via data"
    );
    assert!(
        !influencers_data.contains(&cond_sink),
        "cond_sink doesnt influence sink via data"
    );
    // sink is only influenced by b and its own arg
    assert_eq!(influencers_data.len(), 2);

    Ok(())
}

#[test]
fn test_arg_is_callsite_influencer() -> Result<()> {
    let ctx = crate::test_utils::test_ctx();
    let ctrl_name = ctx.controller_by_name(Identifier::new_intern("influence"))?;
    let sink_arg = crate::test_utils::get_sink_node(&ctx, ctrl_name, "sink1").unwrap();
    let sink_callsite = crate::test_utils::get_callsite_node(&ctx, ctrl_name, "sink1").unwrap();

    let influencers = ctx
        .influencers(sink_callsite, EdgeType::Data)
        .collect::<Vec<_>>();

    assert!(
        influencers.contains(&sink_arg),
        "arg influences callsite through data"
    );

    Ok(())
}

#[test]
fn test_has_ctrl_influence() -> Result<()> {
    let ctx = crate::test_utils::test_ctx();
    let ctrl_name = ctx.controller_by_name(Identifier::new_intern("ctrl_influence"))?;
    let src_a = ctx.controller_argument(ctrl_name, 0).unwrap();
    let src_b = ctx.controller_argument(ctrl_name, 1).unwrap();
    let a_identity =
        crate::test_utils::get_callsite_or_datasink_node(&ctx, ctrl_name, "identity").unwrap();
    let b_identity =
        crate::test_utils::get_callsite_or_datasink_node(&ctx, ctrl_name, "id").unwrap();
    let validate =
        crate::test_utils::get_callsite_or_datasink_node(&ctx, ctrl_name, "validate_foo").unwrap();
    let sink_cs =
        crate::test_utils::get_callsite_or_datasink_node(&ctx, ctrl_name, "sink1").unwrap();

    assert!(
        ctx.has_ctrl_influence(src_a, sink_cs),
        "src_a influences sink"
    );
    assert!(
        ctx.has_ctrl_influence(a_identity, sink_cs),
        "a_prime influences sink"
    );
    assert!(
        ctx.has_ctrl_influence(validate, sink_cs),
        "validate_foo influences sink"
    );
    assert!(
        !ctx.has_ctrl_influence(src_b, sink_cs),
        "src_b doesnt influence sink"
    );
    assert!(
        !ctx.has_ctrl_influence(b_identity, sink_cs),
        "b_prime doesnt influence sink"
    );

    Ok(())
}
