use std::{io::Write, iter::empty, process::exit, sync::Arc};

use paralegal_spdg::{
    Annotation, CallSite, CallSiteOrDataSink, Ctrl, DataSink, DataSource, DataSourceIndex, DefKind,
    HashMap, HashSet, Identifier, MarkerAnnotation, MarkerRefinement, ProgramDescription,
};

pub use paralegal_spdg::rustc_portable::DefId;

use anyhow::{anyhow, bail, ensure, Result};
use indexical::{impls::BitvecArcIndexMatrix, ToIndex};
use itertools::Itertools;

use super::flows_to::CtrlFlowsTo;

use crate::{
    assert_error, assert_warning,
    diagnostics::{CombinatorContext, DiagnosticsRecorder, HasDiagnosticsBase},
};

/// User-defined PDG markers.
pub type Marker = Identifier;

/// The type identifying a controller
pub type ControllerId = DefId;
/// The type identifying a function that is used in call sites.
pub type FunctionId = DefId;

type MarkerIndex = HashMap<Marker, Vec<(DefId, MarkerRefinement)>>;
type FlowsTo = HashMap<ControllerId, CtrlFlowsTo>;

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

/// Data type representing nodes in the SPDG for a particular controller.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Node<'a> {
    /// ControllerId of the node.
    pub ctrl_id: ControllerId,
    /// The data of the node.
    pub typ: NodeType<'a>,
}

impl<'a> Node<'a> {
    /// Transform a Node into the associated Node with typ [`NodeType::CallSite`]
    pub fn associated_call_site(self) -> Option<Node<'a>> {
        self.typ.as_call_site().map(|cs| Node {
            ctrl_id: self.ctrl_id,
            typ: NodeType::CallSite(cs),
        })
    }
}

/// Enum identifying the different types of nodes in the SPDG
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum NodeType<'a> {
    /// Corresponds to [`DataSource::Argument`].
    ControllerArgument(&'a DataSource),

    /// Corresponds to a [`CallSite`] or [`DataSource::FunctionCall`].
    CallSite(&'a CallSite),

    /// Corresponds to a [`DataSink::Argument`].
    CallArgument(&'a DataSink),

    /// Corresponds to a [`DataSink::Return`].
    Return(&'a DataSink),
}

impl<'a> From<&'a CallSite> for NodeType<'a> {
    fn from(cs: &'a CallSite) -> Self {
        NodeType::CallSite(cs)
    }
}

impl<'a> From<&'a DataSink> for NodeType<'a> {
    fn from(ds: &'a DataSink) -> Self {
        match ds {
            DataSink::Argument { .. } => NodeType::CallArgument(ds),
            DataSink::Return => NodeType::Return(ds),
        }
    }
}

impl<'a> From<&'a CallSiteOrDataSink> for NodeType<'a> {
    fn from(x: &'a CallSiteOrDataSink) -> Self {
        match x {
            CallSiteOrDataSink::CallSite(cs) => cs.into(),
            CallSiteOrDataSink::DataSink(ds) => ds.into(),
        }
    }
}

impl<'a> From<&'a DataSource> for NodeType<'a> {
    fn from(ds: &'a DataSource) -> Self {
        match ds {
            DataSource::FunctionCall(cs) => NodeType::CallSite(cs),
            DataSource::Argument(_) => NodeType::ControllerArgument(ds),
        }
    }
}

impl<'a> NodeType<'a> {
    /// Transform a NodeType into it's corresponding CallSite - only works for CallSites and CallArguments.
    pub fn as_call_site(self) -> Option<&'a CallSite> {
        match self {
            NodeType::ControllerArgument(_) => None,
            NodeType::CallSite(cs) => Some(cs),
            NodeType::CallArgument(ds) => match ds {
                DataSink::Argument { function, .. } => Some(function),
                DataSink::Return => None,
            },
            NodeType::Return(_) => None,
        }
    }

    /// Transform a NodeType into it's corresponding DataSink - only works for CallArgs and Returns.
    pub fn as_data_sink(self) -> Option<&'a DataSink> {
        match self {
            NodeType::ControllerArgument(_) => None,
            NodeType::CallSite(_) => None,
            NodeType::CallArgument(ds) => Some(ds),
            NodeType::Return(ds) => Some(ds),
        }
    }

    /// Transform a NodeType into it's corresponding owned CallSiteOrDataSink - only works for CallSites, CallArgs and Returns. Clones the underlying data.
    pub fn as_call_site_or_data_sink(self) -> Option<CallSiteOrDataSink> {
        match self {
            NodeType::ControllerArgument(_) => None,
            NodeType::CallSite(cs) => Some((*cs).clone().into()),
            NodeType::CallArgument(ds) => Some((*ds).clone().into()),
            NodeType::Return(ds) => Some((*ds).clone().into()),
        }
    }

    /// Transform a NodeType into it's corresponding owned DataSource - only works for CtrlArgs, CallSites, and CallArguments. Clones underlying data.
    pub fn as_data_source(self) -> Option<DataSource> {
        match self {
            NodeType::ControllerArgument(ds) => Some((*ds).clone()),
            NodeType::CallSite(cs) => Some(DataSource::FunctionCall((*cs).clone())),
            NodeType::CallArgument(ds) => match ds {
                DataSink::Argument { function, .. } => {
                    Some(DataSource::FunctionCall(function.clone()))
                }
                DataSink::Return => None,
            },
            NodeType::Return(_) => None,
        }
    }
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
        desc.annotations
            .iter()
            .flat_map(|(id, (annots, _))| {
                annots.iter().filter_map(move |annot| match annot {
                    Annotation::Marker(MarkerAnnotation { marker, refinement }) => {
                        Some((*marker, (*id, refinement.clone())))
                    }
                    _ => None,
                })
            })
            .into_group_map()
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
    /// If you use flows_to with [`EdgeType::Control`], you might want to consider using has_ctrl_influence.
    pub fn flows_to(&self, src: Node, sink: Node, edge_type: EdgeType) -> bool {
        if src.ctrl_id != sink.ctrl_id {
            return false;
        }

        // Special case if src is a CallArgument and sink is a CallSite, flows_to is true if they are on the same CallSite.
        if matches!(
            (edge_type, src.typ, sink.typ),
            (EdgeType::Data | EdgeType::DataAndControl,
                NodeType::CallArgument(DataSink::Argument { function, .. }),
                NodeType::CallSite(cs)) if *function == *cs)
        {
            return true;
        }

        let cf_id = &src.ctrl_id;
        let Some(src_datasource) = src.typ.as_data_source() else {
			return false
		  };
        let Some(sink_cs_or_ds) = sink.typ.as_call_site_or_data_sink() else {
			return false
		  };

        match edge_type {
            EdgeType::Data => self.flows_to[cf_id]
                .data_flows_to
                .row_set(&src_datasource.to_index(&self.flows_to[cf_id].sources))
                .contains(sink_cs_or_ds),
            EdgeType::DataAndControl => self.flows_to[cf_id]
                .flows_to
                .row_set(&src_datasource.to_index(&self.flows_to[cf_id].sources))
                .contains(sink_cs_or_ds),
            EdgeType::Control => {
                let cs = match sink.typ.as_call_site() {
                    Some(cs) => cs,
                    None => return false,
                };

                match self.desc.controllers[cf_id].ctrl_flow.get(&src_datasource) {
                    Some(callsites) => callsites.iter().contains(cs),
                    None => false,
                }
            }
        }
    }

    /// Returns whether there is direct control flow influence from influencer to sink, or is there is some data flow from influencer to something that has ctrl flow to sink.
    pub fn has_ctrl_influence(&self, influencer: Node, target: Node) -> bool {
        let Some(tcs) = target.associated_call_site() else {
				return false;
			};

        self.flows_to(influencer, tcs, EdgeType::Control)
            || self
                .influencees(influencer, EdgeType::Data)
                .any(|inf| self.flows_to(inf, tcs, EdgeType::Control))
    }

    /// Returns iterator over all Nodes that influence the given sink Node.
    ///
    /// Does not return the input node. A CallSite sink will return all of the associated CallArgument nodes.
    pub fn influencers<'a>(
        &'a self,
        sink: Node<'a>,
        edge_type: EdgeType,
    ) -> Box<dyn Iterator<Item = Node> + 'a> {
        let cf_id = &sink.ctrl_id;
        let Some(sink_cs_or_ds) = sink.typ.as_call_site_or_data_sink() else {
			return Box::new(empty());
		};

        let controller_flow = &self.flows_to[&sink.ctrl_id];

        let callargs_for_callsite = move |cs: &'a CallSite| {
            controller_flow
                .callsites_to_callargs
                .row_set(
                    &controller_flow
                        .sinks
                        .index(&CallSiteOrDataSink::CallSite(cs.clone())),
                )
                .iter()
                .map(move |ca| Node {
                    ctrl_id: sink.ctrl_id,
                    typ: ca.into(),
                })
        };

        let get_influencers = |flow: &'a BitvecArcIndexMatrix<
            DataSourceIndex,
            CallSiteOrDataSink,
        >| {
            let influencers = flow
                .rows()
                .filter_map(move |(src, row_set)| row_set.contains(&sink_cs_or_ds).then_some(src))
                .flat_map(move |idx| {
                    // We definitely are influenced by the node itself.
                    let mut nodes = vec![Node {
                        ctrl_id: sink.ctrl_id,
                        typ: self.flows_to[&sink.ctrl_id].sources.value(*idx).into(),
                    }];

                    // If the node is a CallSite and has any CallArguments, we are influenced by those as well.
                    if let DataSource::FunctionCall(cs) = controller_flow.sources.value(*idx) {
                        nodes.extend(callargs_for_callsite(cs))
                    }

                    nodes
                });

            // Special case if sink is a callsite, the callargs are also influencers
            let cs_args = if let NodeType::CallSite(cs) = sink.typ {
                Some(callargs_for_callsite(cs))
            } else {
                None
            };
            Box::new(influencers.chain(cs_args.into_iter().flatten()))
        };

        match edge_type {
            EdgeType::Data => get_influencers(&self.flows_to[cf_id].data_flows_to),
            EdgeType::DataAndControl => get_influencers(&self.flows_to[cf_id].flows_to),
            EdgeType::Control => {
                let Some(cs) = sink.typ.as_call_site() else {
					return Box::new(empty());
				};
                Box::new(
                    self.desc.controllers[cf_id]
                        .ctrl_flow
                        .iter()
                        .filter_map(move |(src, sinks)| {
                            sinks.contains(cs).then_some(Node {
                                ctrl_id: sink.ctrl_id,
                                typ: src.into(),
                            })
                        })
                        .flat_map(move |n| {
                            let mut nodes = vec![n];

                            // If the node is a CallSite and has any CallArguments, we are influenced by those as well.
                            if let Some(cs) = n.typ.as_call_site() {
                                nodes.extend(callargs_for_callsite(cs))
                            }

                            nodes
                        }),
                )
            }
        }
    }

    /// Returns iterator over all Nodes that are influenced by the given src Node.
    ///
    /// Does not return the input node. A CallArgument src will return the associated CallSite.
    pub fn influencees<'a>(
        &'a self,
        src: Node<'a>,
        edge_type: EdgeType,
    ) -> Box<dyn Iterator<Item = Node> + 'a> {
        let cf_id = &src.ctrl_id;
        let Some(src_datasource) = src.typ.as_data_source() else {
			return Box::new(empty());
		};

        let get_influencees =
            |flow: &'a BitvecArcIndexMatrix<DataSourceIndex, CallSiteOrDataSink>| {
                let influencees = flow
                    .row_set(
                        &src_datasource
                            .clone()
                            .to_index(&self.flows_to[cf_id].sources),
                    )
                    .iter()
                    .flat_map(move |cs_ds| {
                        // We definitely influence to the node itself.
                        let mut nodes = vec![Node {
                            ctrl_id: src.ctrl_id,
                            typ: cs_ds.into(),
                        }];
                        // If the node is a DataSink::Argument, we influence it's corresponding CallSite as well.
                        if let CallSiteOrDataSink::DataSink(DataSink::Argument {
                            function: f,
                            ..
                        }) = cs_ds
                        {
                            nodes.push(Node {
                                ctrl_id: src.ctrl_id,
                                typ: f.into(),
                            })
                        }
                        nodes
                    });

                // Special case if sink is callarg, callsite is also an influencer
                let arg_cs =
                    if let NodeType::CallArgument(DataSink::Argument { function, .. }) = src.typ {
                        Some(Node {
                            ctrl_id: src.ctrl_id,
                            typ: function.into(),
                        })
                    } else {
                        None
                    };
                Box::new(influencees.chain(arg_cs.into_iter()))
            };

        match edge_type {
            EdgeType::Data => get_influencees(&self.flows_to[cf_id].data_flows_to),
            EdgeType::DataAndControl => get_influencees(&self.flows_to[cf_id].flows_to),
            EdgeType::Control => {
                match self.desc.controllers[cf_id].ctrl_flow.get(&src_datasource) {
                    Some(callsites) => Box::new(callsites.iter().map(move |cs| Node {
                        ctrl_id: src.ctrl_id,
                        typ: cs.into(),
                    })),
                    None => Box::new(empty()),
                }
            }
        }
    }

    /// Returns an iterator over all objects marked with `marker`.
    pub fn marked(
        &self,
        marker: Marker,
    ) -> impl Iterator<Item = &'_ (DefId, MarkerRefinement)> + '_ {
        self.report_marker_if_absent(marker);
        self.marker_to_ids
            .get(&marker)
            .into_iter()
            .flat_map(|v| v.iter())
    }

    /// Get the type(s) of a Node.
    pub fn get_node_types(&self, node: &Node) -> Option<&HashSet<DefId>> {
        match node.typ.as_data_source() {
            None => None,
            Some(src) => self.desc.controllers[&node.ctrl_id].types.get(&src),
        }
    }

    /// Returns whether the given Node has the marker applied to it directly or via its type.
    pub fn has_marker(&self, marker: Marker, node: Node) -> bool {
        if let Some(types) = self.get_node_types(&node) {
            if types.iter().any(|t| {
                self.marker_to_ids
                    .get(&marker)
                    .map(|markers| markers.iter().any(|(id, _)| id == t))
                    .unwrap_or(false)
            }) {
                return true;
            }
        }

        /// Return whether marker is on something with the given name's self or the argument at arg
        fn marker_on_argument(ctx: &Context, marker: Marker, name: DefId, arg: usize) -> bool {
            ctx.marker_to_ids
                .get(&marker)
                .map(|markers| {
                    markers.iter().any(|(id, refinement)| {
                        id == &name
                            && (refinement.on_self()
                                || refinement.on_argument().contains(arg as u32).unwrap())
                    })
                })
                .unwrap_or(false)
        }
        /// Return whether marker is on something with the given name's self or the return
        fn marker_on_return(ctx: &Context, marker: Marker, name: DefId) -> bool {
            ctx.marker_to_ids
                .get(&marker)
                .map(|markers| {
                    markers.iter().any(|(id, refinement)| {
                        id == &name && (refinement.on_self() || refinement.on_return())
                    })
                })
                .unwrap_or(false)
        }

        match node.typ {
            NodeType::ControllerArgument(source) => match source {
                DataSource::Argument(arg) => marker_on_argument(self, marker, node.ctrl_id, *arg),
                DataSource::FunctionCall(_) => {
                    panic!("impossible - CtrlArgument variant cannot be DataSource::FunctionCall")
                }
            },
            NodeType::CallSite(cs) => marker_on_return(self, marker, cs.function),
            NodeType::CallArgument(ds) => match ds {
                DataSink::Argument { function, arg_slot } => {
                    marker_on_argument(self, marker, function.function, *arg_slot)
                }
                DataSink::Return => {
                    panic!("impossible - CallArgument variant cannot be DataSink::Return")
                }
            },
            NodeType::Return(_) => marker_on_return(self, marker, node.ctrl_id),
        }
    }

    /// Returns all DataSources, DataSinks, and CallSites for a Controller as Nodes.
    pub fn all_nodes_for_ctrl(&self, ctrl_id: ControllerId) -> impl Iterator<Item = Node<'_>> {
        let ctrl = &self.desc.controllers[&ctrl_id];
        ctrl.all_sources()
            .map(move |src| Node {
                ctrl_id,
                typ: src.into(),
            })
            .chain(ctrl.data_sinks().map(move |snk| Node {
                ctrl_id,
                typ: snk.into(),
            }))
            .chain(ctrl.call_sites().map(move |cs| Node {
                ctrl_id,
                typ: cs.into(),
            }))
            .unique()
    }

    /// Returns an iterator over the data sources within controller `c` that have type `t`.
    pub fn srcs_with_type(&self, ctrl_id: ControllerId, t: DefId) -> impl Iterator<Item = Node> {
        self.desc.controllers[&ctrl_id]
            .types
            .0
            .iter()
            .filter_map(move |(src, ids)| {
                ids.contains(&t).then_some(Node {
                    ctrl_id,
                    typ: src.into(),
                })
            })
    }

    /// Returns an iterator over all nodes that do not have any influencers of the given edge_type.
    pub fn roots(&self, ctrl_id: ControllerId, edge_type: EdgeType) -> impl Iterator<Item = Node> {
        self.all_nodes_for_ctrl(ctrl_id)
            .filter(move |n| self.influencers(*n, edge_type).next().is_none())
    }

    /// Returns the input [`ProgramDescription`].
    pub fn desc(&self) -> &ProgramDescription {
        &self.desc
    }

    /// Returns all the [`Annotation::OType`]s for a controller `id`.
    pub fn otypes(&self, id: DefId) -> Vec<DefId> {
        self.desc()
            .annotations
            .get(&id)
            .into_iter()
            .flat_map(|(anns, _)| {
                anns.iter().filter_map(|annot| match annot {
                    Annotation::OType(id) => Some(*id),
                    _ => None,
                })
            })
            .collect()
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
    pub fn always_happens_before<'a>(
        &self,
        starting_points: impl Iterator<Item = Node<'a>>,
        mut is_checkpoint: impl FnMut(Node) -> bool,
        mut is_terminal: impl FnMut(Node) -> bool,
    ) -> Result<AlwaysHappensBefore> {
        let mut seen = HashSet::<&DataSink>::new();
        let mut num_reached = 0;
        let mut num_checkpointed = 0;

        // Return whether node is checkpoint or terminal and increment those respective counters
        let mut check_node = |node: Node| -> bool {
            if is_checkpoint(node) {
                num_checkpointed += 1;
                return true;
            } else if is_terminal(node) {
                num_reached += 1;
                return true;
            }
            false
        };

        let starts = starting_points.collect::<Vec<_>>();
        let started_with = starts.len();

        let mut queue = starts
            .iter()
            .filter_map(|n| {
                if check_node(*n) {
                    return None;
                }
                match n.typ.as_data_source() {
                    Some(ds) => Some((
                        ds,
                        n.ctrl_id,
                        &self.desc().controllers.get(&n.ctrl_id).unwrap().data_flow.0,
                    )),
                    None => {
                        assert_warning!(
                            *self,
                            false,
                            format!(
                            "found starting point {:?} that cannot be converted to a datasource",
                            n
                        )
                        );
                        None
                    }
                }
            })
            .collect::<Vec<_>>();

        while let Some(current) = queue.pop() {
            // Check the datasource.
            if check_node(Node {
                ctrl_id: current.1,
                typ: (&current.0).into(),
            }) {
                continue;
            }

            // Check all sinks the source flows to.
            for sink in current.2.get(&current.0).into_iter().flatten() {
                if check_node(Node {
                    ctrl_id: current.1,
                    typ: sink.into(),
                }) {
                    continue;
                } else if let DataSink::Argument { function, .. } = sink {
                    // If the sink is an argument, it can be converted to a datasource and added to the queue.
                    if seen.insert(sink) {
                        queue.push((function.clone().into(), current.1, current.2));
                    }
                }
            }
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
    pub fn marked_type<'a>(&'a self, marker: Marker) -> impl Iterator<Item = DefId> + 'a {
        self.report_marker_if_absent(marker);
        self.marked(marker)
            .filter(|(did, _)| self.desc().def_info[did].kind == DefKind::Type)
            .map(|(did, refinement)| {
                assert!(refinement.on_self());
                *did
            })
    }

    /// Return an example pair for a flow from an source from `from` to a sink
    /// in `to` if any exist.
    pub fn any_flows<'a>(
        &'a self,
        from: &[Node<'a>],
        to: &[Node<'a>],
        edge_type: EdgeType,
    ) -> Option<(Node, Node)> {
        from.iter().find_map(|src| {
            to.iter().find_map(|sink| {
                self.flows_to(*src, *sink, edge_type)
                    .then_some((*src, *sink))
            })
        })
    }

    /// Iterate over all defined controllers
    pub fn all_controllers(&self) -> impl Iterator<Item = (ControllerId, &Ctrl)> {
        self.desc().controllers.iter().map(|(k, v)| (*k, v))
    }

    /// Returns a DisplayDef for the given def_id
    pub fn describe_def(&self, def_id: DefId) -> DisplayDef {
        DisplayDef { ctx: self, def_id }
    }

    /// Returns a DisplayNode for the given Node
    pub fn describe_node<'a>(&'a self, node: Node<'a>) -> DisplayNode<'a> {
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
    pub node: Node<'a>,
    /// Context for the Node.
    pub ctx: &'a Context,
}

impl<'a> std::fmt::Display for DisplayNode<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Controller:")?;
        self.ctx.describe_def(self.node.ctrl_id).fmt(f)?;
        f.write_str("\n")?;

        match self.node.typ {
            NodeType::ControllerArgument(ds) => match ds {
                DataSource::FunctionCall(_) => panic!("impossible"),
                DataSource::Argument(pos) => {
                    f.write_fmt(format_args!("ControllerArgument:{:}", pos))
                }
            },
            NodeType::CallSite(cs) => {
                f.write_str("CallSite:")?;
                self.ctx.describe_def(cs.function).fmt(f)
            }
            NodeType::CallArgument(ds) => match ds {
                DataSink::Argument { function, arg_slot } => {
                    f.write_str("CallArgument:")?;
                    self.ctx.describe_def(function.function).fmt(f)?;
                    f.write_fmt(format_args!(":{:}", arg_slot))
                }
                DataSink::Return => panic!("impossible"),
            },
            NodeType::Return(_) => f.write_str("Return"),
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
    assert!(ctx.marked(Marker::new_intern("input")).any(|(id, _)| ctx
        .desc
        .def_info
        .get(id)
        .map_or(false, |info| info.name.as_str().starts_with("Foo"))));

    let controller = ctx.find_by_name("controller").unwrap();

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

    fn is_terminal(end: Node<'_>) -> bool {
        matches!(end.typ, crate::NodeType::Return(_))
    }

    let ctrl_name = ctx.find_by_name("happens_before_pass")?;

    let pass = ctx.always_happens_before(
        ctx.all_nodes_for_ctrl(ctrl_name)
            .filter(|n| ctx.has_marker(Identifier::new_intern("start"), *n)),
        |checkpoint| ctx.has_marker(Identifier::new_intern("bless"), checkpoint),
        is_terminal,
    )?;

    ensure!(pass.holds());
    ensure!(!pass.is_vacuous(), "{pass}");

    let ctrl_name = ctx.find_by_name("happens_before_fail")?;

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
    let ctrl_name = ctx.find_by_name("influence")?;
    let src_a = crate::Node {
        ctrl_id: ctrl_name,
        typ: (&DataSource::Argument(0)).into(),
    };
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
    let ctrl_name = ctx.find_by_name("influence")?;
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
    let ctrl_name = ctx.find_by_name("influence")?;
    let src_a = crate::Node {
        ctrl_id: ctrl_name,
        typ: (&DataSource::Argument(0)).into(),
    };
    let src_b = crate::Node {
        ctrl_id: ctrl_name,
        typ: (&DataSource::Argument(1)).into(),
    };
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
    let ctrl_name = ctx.find_by_name("influence")?;
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
    let ctrl_name = ctx.find_by_name("ctrl_influence")?;
    let src_a = crate::Node {
        ctrl_id: ctrl_name,
        typ: (&DataSource::Argument(0)).into(),
    };
    let src_b = crate::Node {
        ctrl_id: ctrl_name,
        typ: (&DataSource::Argument(1)).into(),
    };
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
