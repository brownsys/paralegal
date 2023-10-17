use std::{io::Write, process::exit, sync::Arc};

use paralegal_spdg::{
    Annotation, CallSite, CallSiteOrDataSink, Ctrl, DataSink, DataSource, DefKind, HashMap,
    HashSet, Identifier, MarkerAnnotation, MarkerRefinement, ProgramDescription,
};

pub use paralegal_spdg::rustc_portable::DefId;

use anyhow::{anyhow, bail, ensure, Result};
use indexical::ToIndex;
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
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct CtrlNode<'a> {
    /// ControllerId of the node.
    pub ctrl_id: &'a ControllerId,
    /// The data of the node.
    pub node: Node<'a>,
}

/// Enum identifying the different types of nodes in the SPDG
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Node<'a> {
    /// Corresponds to [`DataSource::Argument`].
    CtrlArgument(&'a DataSource),

    /// Corresponds to a [`CallSite`] or [`DataSource::FunctionCall`].
    CallSite(&'a CallSite),

    /// Corresponds to a [`DataSink::Argument`].
    CallArgument(&'a DataSink),

    /// Corresponds to a [`DataSink::Return`].
    Return(&'a DataSink),
}

impl<'a> From<&'a CallSite> for Node<'a> {
    fn from(cs: &'a CallSite) -> Self {
        Node::CallSite(cs)
    }
}

impl<'a> From<&'a DataSink> for Node<'a> {
    fn from(ds: &'a DataSink) -> Self {
        match ds {
            DataSink::Argument { .. } => Node::CallArgument(ds),
            DataSink::Return => Node::Return(ds),
        }
    }
}

impl<'a> From<&'a CallSiteOrDataSink> for Node<'a> {
    fn from(x: &'a CallSiteOrDataSink) -> Self {
        match x {
            CallSiteOrDataSink::CallSite(cs) => cs.into(),
            CallSiteOrDataSink::DataSink(ds) => ds.into(),
        }
    }
}

impl<'a> From<&'a DataSource> for Node<'a> {
    fn from(ds: &'a DataSource) -> Self {
        match ds {
            DataSource::FunctionCall(cs) => Node::CallSite(cs),
            DataSource::Argument(_) => Node::CtrlArgument(ds),
        }
    }
}

impl<'a> Node<'a> {
    /// Transform a Node into it's corresponding CallSite - only works for CallSites and CallArguments.
    pub fn as_call_site(&self) -> Option<&CallSite> {
        match self {
            Node::CtrlArgument(_) => None,
            Node::CallSite(cs) => Some(cs),
            Node::CallArgument(ds) => match ds {
                DataSink::Argument { function, .. } => Some(function),
                DataSink::Return => None,
            },
            Node::Return(_) => None,
        }
    }

    /// Transform a Node into it's corresponding DataSink - only works for CallArgs and Returns.
    pub fn as_data_sink(&self) -> Option<&DataSink> {
        match self {
            Node::CtrlArgument(_) => None,
            Node::CallSite(_) => None,
            Node::CallArgument(ds) => Some(ds),
            Node::Return(ds) => Some(ds),
        }
    }

    /// Transform a Node into it's corresponding owned CallSiteOrDataSink - only works for CallSites, CallArgs and Returns. Clones the underlying data.
    pub fn as_call_site_or_data_sink(&self) -> Option<CallSiteOrDataSink> {
        match self {
            Node::CtrlArgument(_) => None,
            Node::CallSite(cs) => Some((*cs).clone().into()),
            Node::CallArgument(ds) => Some((*ds).clone().into()),
            Node::Return(ds) => Some((*ds).clone().into()),
        }
    }

    /// Transform a Node into it's corresponding owned DataSource - only works for CtrlArgs, CallSites, and CallArguments. Clones underlying data.
    pub fn as_data_source(&self) -> Option<DataSource> {
        match self {
            Node::CtrlArgument(ds) => Some((*ds).clone()),
            Node::CallSite(cs) => Some(DataSource::FunctionCall((*cs).clone())),
            Node::CallArgument(ds) => match ds {
                DataSink::Argument { function, .. } => {
                    Some(DataSource::FunctionCall(function.clone()))
                }
                DataSink::Return => None,
            },
            Node::Return(_) => None,
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
    pub(crate) diagnostics: Arc<DiagnosticsRecorder>,
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
    pub fn emit_diagnostics(&self, w: impl Write) -> Result<()> {
        if !self.diagnostics.emit(w)? {
            exit(1)
        }
        Ok(())
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

    /// Returns whether a node or set of nodes that match some condition flows to a node or set of nodes that match another condition through the configured edge type.
    pub fn flows_to(&self, src: &CtrlNode, sink: &CtrlNode, edge_type: EdgeType) -> bool {
        if src.ctrl_id != sink.ctrl_id {
            return false;
        }

        let cf_id = &src.ctrl_id;
        let src_datasource = match src.node.as_data_source() {
            Some(ds) => ds,
            None => return false,
        };
        let sink_cs_or_ds = match sink.node.as_call_site_or_data_sink() {
            Some(s) => s,
            None => return false,
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
                let cs = match sink.node.as_call_site() {
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

    /// Returns an iterator over all objects marked with `marker`.
    pub fn marked(
        &self,
        marker: Marker,
    ) -> impl Iterator<Item = &'_ (DefId, MarkerRefinement)> + '_ {
        self.marker_to_ids
            .get(&marker)
            .into_iter()
            .flat_map(|v| v.iter())
    }

    /// Returns whether the given CtrlNode has the marker applied to it directly or via its type.
    pub fn has_marker(&self, marker: Marker, node: &CtrlNode) -> bool {
        match node.node {
            Node::CtrlArgument(_) => false, // TODO: complete
            Node::CallSite(_) => false,     // TODO: complete
            Node::CallArgument(ds) => match ds {
                DataSink::Argument { function, arg_slot } => self
                    .marker_to_ids
                    .get(&marker)
                    .map(|markers| {
                        markers.iter().any(|(id, refinement)| {
                            id == &function.function
                                && (refinement.on_self()
                                    || refinement.on_argument().contains(*arg_slot as u32).unwrap())
                        })
                    })
                    .unwrap_or(false),
                // TODO: check the type as well
                DataSink::Return => {
                    panic!("impossible - CallArgument variant cannot be DataSink::Return")
                }
            },
            Node::Return(_) => false, // TODO: complete
        }
    }

    /// Returns all DataSources, DataSinks, and CallSites for a Controller as CtrlNodes.
    pub fn all_nodes_for_ctrl<'a>(
        &'a self,
        ctrl_id: &'a ControllerId,
    ) -> impl Iterator<Item = CtrlNode<'a>> {
        let ctrl = &self.desc.controllers[ctrl_id];
        ctrl.all_sources()
            .map(|src| CtrlNode {
                ctrl_id,
                node: src.into(),
            })
            .chain(ctrl.data_sinks().map(|snk| CtrlNode {
                ctrl_id,
                node: snk.into(),
            }))
            .chain(ctrl.call_sites().map(|cs| CtrlNode {
                ctrl_id,
                node: cs.into(),
            }))
    }

    /// Returns an iterator over the data sources within controller `c` that have type `t`.
    pub fn srcs_with_type<'a>(
        &'a self,
        ctrl_id: &'a ControllerId,
        t: DefId,
    ) -> impl Iterator<Item = CtrlNode> + 'a {
        self.desc.controllers[ctrl_id]
            .types
            .0
            .iter()
            .filter_map(move |(src, ids)| {
                ids.contains(&t).then_some(CtrlNode {
                    ctrl_id,
                    node: src.into(),
                })
            })
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

    /// Enforce that on every path from the `starting_points` to `is_terminal` a
    /// node satisfying `is_checkpoint` is passed.
    ///
    /// Fails if `ctrl` is not found.
    ///
    /// The return value contains some statistics information about the
    /// traversal. The property holds if [`AlwaysHappensBefore::holds`] is true.
    ///
    /// Note that `is_checkpoint` and `is_terminal` will be called many times
    /// and should thus be efficient computations. In addition they should
    /// always return the same result for the same input.
    pub fn always_happens_before(
        &self,
        ctrl: ControllerId,
        starting_points: impl Iterator<Item = DataSource>,
        mut is_checkpoint: impl FnMut(&DataSink) -> bool,
        mut is_terminal: impl FnMut(&DataSink) -> bool,
    ) -> Result<AlwaysHappensBefore> {
        let mut seen = HashSet::<&DataSink>::new();
        let mut num_reached = 0;
        let mut num_checkpointed = 0;

        let mut queue = starting_points.collect::<Vec<_>>();

        let started_with = queue.len();

        let flow = &self
            .desc()
            .controllers
            .get(&ctrl)
            .ok_or_else(|| anyhow!("Controller not found"))?
            .data_flow
            .0;

        while let Some(current) = queue.pop() {
            for sink in flow.get(&current).into_iter().flatten() {
                if is_checkpoint(sink) {
                    num_checkpointed += 1;
                } else if is_terminal(sink) {
                    num_reached += 1;
                } else if let DataSink::Argument { function, .. } = sink {
                    if seen.insert(sink) {
                        queue.push(DataSource::FunctionCall(function.clone()));
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
        from: &[&'a CtrlNode],
        to: &[&'a CtrlNode],
        edge_type: EdgeType,
    ) -> Option<(&'a CtrlNode, &'a CtrlNode)> {
        from.iter().find_map(|&src| {
            to.iter()
                .find_map(|&sink| self.flows_to(src, sink, edge_type).then_some((src, sink)))
        })
    }

    /// Iterate over all defined controllers
    pub fn all_controllers(&self) -> impl Iterator<Item = (ControllerId, &Ctrl)> {
        self.desc().controllers.iter().map(|(k, v)| (*k, v))
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
    let input = Marker::new_intern("input");
    let sink = Marker::new_intern("sink");
    assert!(ctx.marked(input).any(|(id, _)| ctx
        .desc
        .def_info
        .get(id)
        .map_or(false, |info| info.name.as_str().starts_with("Foo"))));

    let controller = ctx.find_by_name("controller").unwrap();

    assert_eq!(
        ctx.all_nodes_for_ctrl(&controller)
            .filter(|n| ctx.has_marker(input, n))
            .count(),
        0
    );
    assert_eq!(
        ctx.all_nodes_for_ctrl(&controller)
            .filter(|n| ctx.has_marker(sink, n))
            .count(),
        2
    );
}

#[test]
fn test_happens_before() -> Result<()> {
    let ctx = crate::test_utils::test_ctx();
    let desc = ctx.desc();

    fn has_marker(desc: &ProgramDescription, sink: &DataSink, marker: Identifier) -> bool {
        if let DataSink::Argument { function, arg_slot } = sink {
            desc.annotations
                .get(&function.function)
                .map_or(false, |(anns, _)| {
                    anns.iter().filter_map(Annotation::as_marker).any(|ann| {
                        ann.marker == marker
                            && (ann
                                .refinement
                                .on_argument()
                                .contains(*arg_slot as u32)
                                .unwrap()
                                || ann.refinement.on_self())
                    })
                })
        } else {
            false
        }
    }

    fn is_checkpoint(desc: &ProgramDescription, checkpoint: &DataSink) -> bool {
        has_marker(desc, checkpoint, Identifier::new_intern("bless"))
    }
    fn is_terminal(end: &DataSink) -> bool {
        matches!(end, DataSink::Return)
    }

    fn marked_sources(
        desc: &ProgramDescription,
        ctrl_name: DefId,
        marker: Marker,
    ) -> impl Iterator<Item = &DataSource> {
        desc.controllers[&ctrl_name]
            .data_flow
            .0
            .keys()
            .filter(move |source| match source {
                DataSource::Argument(arg) => desc.annotations[&ctrl_name]
                    .0
                    .iter()
                    .filter_map(Annotation::as_marker)
                    .any(|ann| {
                        ann.marker == marker
                            && (ann.refinement.on_self()
                                || ann
                                    .refinement
                                    .on_argument()
                                    .contains(*arg as u32)
                                    .unwrap_or(false))
                    }),
                DataSource::FunctionCall(cs) => desc.annotations[&cs.function]
                    .0
                    .iter()
                    .filter_map(Annotation::as_marker)
                    .any(|ann| {
                        ann.marker == marker
                            && (ann.refinement.on_self() || ann.refinement.on_return())
                    }),
            })
    }

    let ctrl_name = ctx.find_by_name("happens_before_pass")?;

    let pass = ctx.always_happens_before(
        ctrl_name,
        marked_sources(desc, ctrl_name, Identifier::new_intern("start")).cloned(),
        |checkpoint| is_checkpoint(desc, checkpoint),
        is_terminal,
    )?;

    ensure!(pass.holds());
    ensure!(!pass.is_vacuous(), "{pass}");

    let ctrl_name = ctx.find_by_name("happens_before_fail")?;

    let fail = ctx.always_happens_before(
        ctrl_name,
        marked_sources(desc, ctrl_name, Identifier::new_intern("start")).cloned(),
        |check| is_checkpoint(desc, check),
        is_terminal,
    )?;

    ensure!(!fail.holds());
    ensure!(!fail.is_vacuous());

    Ok(())
}
