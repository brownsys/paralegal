use std::{
    io::{self, Write},
    process::exit,
    sync::Arc,
};

use paralegal_spdg::{
    utils::{write_sep, Print},
    Annotation, CallSite, CallSiteOrDataSink, Ctrl, DataSink, DataSource, DefInfo, DefKind,
    HashMap, HashSet, Identifier, MarkerAnnotation, MarkerRefinement, ProgramDescription,
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

/// Interface for defining policies.
///
/// Holds a PDG ([`Self::desc`]) and defines basic queries like
/// [`Self::marked_sinks`] and combinators such as
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
    pub fn emit_diagnostics(&self, w: impl Write) -> Result<()> {
        if !self.diagnostics.emit(w)? {
            exit(1)
        }
        Ok(())
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

    /// Returns true if `src` has a data-flow to `sink` in the controller `ctrl_id`
    pub fn data_flows_to(&self, ctrl_id: ControllerId, src: &DataSource, sink: &DataSink) -> bool {
        let ctrl_flows = &self.flows_to[&ctrl_id];
        ctrl_flows
            .data_flows_to
            .row_set(&src.to_index(&ctrl_flows.sources))
            .contains(CallSiteOrDataSink::DataSink(sink.clone()))
    }

    /// Returns true if `src` has a data+ctrl-flow to `sink` in the controller `ctrl_id`
    pub fn flows_to(
        &self,
        ctrl_id: ControllerId,
        src: &DataSource,
        sink: &CallSiteOrDataSink,
    ) -> bool {
        let ctrl_flows = &self.flows_to[&ctrl_id];
        ctrl_flows
            .flows_to
            .row_set(&src.to_index(&ctrl_flows.sources))
            .contains(sink)
    }

    /// Return a set of all sinks this source can reach
    pub fn reaching(&self, ctrl_id: ControllerId, src: &DataSource) -> &indexical::IndexSet<CallSiteOrDataSink, bitvec::vec::BitVec, indexical::ArcFamily> {
        let ctrl_flows = &self.flows_to[&ctrl_id];
        ctrl_flows
            .flows_to
            .row_set(&src.to_index(&ctrl_flows.sources))
    }

    /// Iterate all sinks that are reachable from this source in the given controller.
    pub fn reachable(
        &self,
        ctrl_id: ControllerId,
        src: &DataSource,
    ) -> impl Iterator<Item = &DataSink> {
        let ctrl_flows = &self.flows_to[&ctrl_id];
        ctrl_flows
            .flows_to
            .row_set(&src.to_index(&ctrl_flows.sources))
            .iter()
            .filter_map(CallSiteOrDataSink::as_data_sink)
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

    /// Returns an iterator over all sinks marked with `marker` out of the provided `dsts`.
    pub fn marked_sinks<'a>(
        &'a self,
        dsts: impl IntoIterator<Item = &'a DataSink> + 'a,
        marker: Marker,
    ) -> impl Iterator<Item = &'a DataSink> + 'a {
        self.report_marker_if_absent(marker);
        dsts.into_iter().filter(move |dst| match dst {
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
            _ => false,
        })
    }

    /// Returns an iterator over all the call sites marked with `marker` out of the provided `dsts`.
    pub fn marked_callsites<'a>(
        &'a self,
        dsts: impl IntoIterator<Item = &'a DataSink> + 'a,
        marker: Marker,
    ) -> impl Iterator<Item = &'a CallSite> + 'a {
        self.report_marker_if_absent(marker);
        self.marked_sinks(dsts, marker)
            .filter_map(|sink| match sink {
                DataSink::Argument { function, .. } => Some(function),
                _ => None,
            })
    }

    /// Returns an iterator over the data sources within controller `c` that have type `t`.
    pub fn srcs_with_type<'a>(
        &self,
        c: &'a Ctrl,
        t: DefId,
    ) -> impl Iterator<Item = &'a DataSource> + 'a {
        c.types
            .0
            .iter()
            .filter_map(move |(src, ids)| ids.contains(&t).then_some(src))
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
    pub fn always_happens_before<C: FnMut(&DataSink) -> bool>(
        &self,
        ctrl: ControllerId,
        starting_points: impl Iterator<Item = DataSource>,
        mut is_checkpoint: C,
        mut is_terminal: impl FnMut(&DataSink) -> bool,
    ) -> Result<AlwaysHappensBefore<C>> {
        let mut seen = HashSet::<&DataSink>::new();
        let mut reached = vec![];
        let mut checkpointed = vec![];

        let mut queue = starting_points
            .zip(std::iter::repeat(true))
            .collect::<Vec<_>>();

        let started_with = queue.len();

        let flow = &self
            .desc()
            .controllers
            .get(&ctrl)
            .ok_or_else(|| anyhow!("Controller not found"))?
            .data_flow
            .0;

        let mut current_start = None;
        while let Some((current, is_start)) = queue.pop() {
            if is_start {
                current_start.replace(current.clone());
            }
            for sink in flow.get(&current).into_iter().flatten() {
                if is_checkpoint(sink) {
                    checkpointed.push((current_start.clone().unwrap(), sink.clone()));
                } else if is_terminal(sink) {
                    reached.push((current_start.clone().unwrap(), sink.clone()));
                } else if let DataSink::Argument { function, .. } = sink {
                    if seen.insert(sink) {
                        queue.push((DataSource::FunctionCall(function.clone()), false));
                    }
                }
            }
        }

        Ok(AlwaysHappensBefore {
            reached,
            checkpointed,
            started_with,
            ctrl,
            is_checkpoint,
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

    /// Return an example pair for a data flow from an source from `from` to a sink
    /// in `to` if any exist.
    pub fn any_data_flows<'a>(
        &self,
        ctrl_id: ControllerId,
        from: &[&'a DataSource],
        to: &[&'a DataSink],
    ) -> Option<(&'a DataSource, &'a DataSink)> {
        from.iter().find_map(|&src| {
            to.iter().find_map(|&sink| {
                self.data_flows_to(ctrl_id, src, sink)
                    .then_some((src, sink))
            })
        })
    }

    /// Iterate over all defined controllers
    pub fn all_controllers(&self) -> impl Iterator<Item = (ControllerId, &Ctrl)> {
        self.desc().controllers.iter().map(|(k, v)| (*k, v))
    }

    /// A debugging tool that performs a DFS to return some sequence of nodes
    /// that connect `from` to `to`.
    pub fn a_path_between(
        &self,
        ctrl_id: ControllerId,
        from: &DataSource,
        to: &DataSink,
        mut disallowed: impl FnMut(&DataSink) -> bool,
    ) -> Option<Vec<&DataSink>> {
        let flows_to = &self.flows_to[&ctrl_id];
        let to_as_either = &CallSiteOrDataSink::DataSink(to.clone());
        let ctrl = &self.desc.controllers[&ctrl_id];
        let successors = |from| ctrl.data_flow[&from].iter().peekable();
        let mut path = vec![(None, successors(from.clone()))];
        let mut seen = HashSet::new();

        while let Some((_, nexts)) = path.last_mut() {
            if let Some(next) = nexts.next() {
                if next == to {
                    return Some(path.into_iter().filter_map(|(snk, _)| snk).collect());
                }
                if !seen.insert(next) || disallowed(next) {
                    continue;
                }
                let cs = match next {
                    DataSink::Argument {
                        function,
                        arg_slot: _,
                    } => function,
                    DataSink::Return => {
                        continue;
                    }
                };
                let src = DataSource::FunctionCall(cs.clone());

                if flows_to.sources.contains(&src)
                    && flows_to
                        .data_flows_to
                        .row_set(&(&src).to_index(&flows_to.sources))
                        .contains(to_as_either)
                {
                    path.push((Some(next), successors(src)));
                }
            } else {
                path.pop();
            }
        }
        None
    }

    /// Returns a struct with a `std::fmt::Display` implementation that
    /// pretty-prints the information this context has stored about this
    /// definition.
    pub fn describe_def(&self, def_id: DefId) -> DisplayDef {
        DisplayDef { ctx: self, def_id }
    }
}

/// See [`Context::describe_def`]
pub struct DisplayDef<'a> {
    def_id: DefId,
    ctx: &'a Context,
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
pub struct AlwaysHappensBefore<C> {
    /// How many paths terminated at the end?
    reached: Vec<(DataSource, DataSink)>,
    /// How many paths lead to the checkpoints?
    checkpointed: Vec<(DataSource, DataSink)>,
    /// How large was the set of initial nodes this traversal started with.
    started_with: usize,
    ctrl: ControllerId,
    is_checkpoint: C,
}

/// See [`AlwaysHappensBefore::display`].
pub struct AlwaysHappensBeforeDisplay<'a, C, Ctx> {
    data: &'a AlwaysHappensBefore<C>,
    ctx: Ctx,
}

impl<C, Ctx: HasDiagnosticsBase> std::fmt::Display for AlwaysHappensBeforeDisplay<'_, C, Ctx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.format(f, &self.ctx.as_ctx().desc().def_info)
    }
}

fn fmt_path<'a>(
    f: &mut std::fmt::Formatter<'_>,
    path: impl IntoIterator<Item = &'a DataSink>,
    def_info: &HashMap<DefId, DefInfo>,
) -> std::fmt::Result {
    for node in path {
        writeln!(f)?;
        match node {
            DataSink::Argument { function, arg_slot } => {
                writeln!(
                    f,
                    "  influences {}",
                    Print(|f| {
                        fmt_function(f, function.function, def_info)?;
                        write!(f, "({arg_slot})")
                    })
                )?;
                for fun in function.location.as_slice().iter().rev() {
                    write!(f, "    called in ")?;
                    fmt_function(f, fun.function, def_info)?;
                    writeln!(f)?;
                }
                Ok(())
            }
            DataSink::Return => f.write_str("return\n"),
        }?;
    }
    Ok(())
}

impl<C> AlwaysHappensBefore<C> {
    /// Create a struct that can format the results of this combinator with
    /// [`std::fmt::Display`]
    pub fn display<'a, Ctx: HasDiagnosticsBase>(
        &'a self,
        ctx: Ctx,
    ) -> AlwaysHappensBeforeDisplay<'a, C, Ctx> {
        AlwaysHappensBeforeDisplay { data: self, ctx }
    }

    pub fn record_violations(
        &mut self,
        ctx: impl HasDiagnosticsBase,
        file: &mut impl io::Write,
    ) -> io::Result<()>
    where
        C: FnMut(&DataSink) -> bool,
    {
        let def_info = &ctx.as_ctx().desc().def_info;
        let Some((from, to)) = self.reached.first() else {
            return Ok(());
        };
        let path =
            ctx.as_ctx()
                .a_path_between(self.ctrl, from, to, &mut self.is_checkpoint);
        writeln!(
            file,
            "{}",
            Print(|f| {
                fmt_data_source(from, f, def_info)?;
                if let Some(path) = &path {
                    fmt_path(f, path.into_iter().copied(), def_info)
                } else {
                    write!(f, "Invariant broken: No path found")
                }
            })
        )
    }

    /// Format the results of this combinator, using the `def_info` to print
    /// readable names instead of ids
    pub fn format(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        def_info: &HashMap<DefId, DefInfo>,
    ) -> std::fmt::Result {
        let Self {
            reached,
            checkpointed,
            started_with,
            ..
        } = self;
        writeln!(
            f,
            "{} paths reached the terminal, \
            {} paths reached the checkpoints, \
            started with {started_with} nodes",
            reached.len(),
            checkpointed.len()
        )?;
        let fmt_from_to = |(from, to): &(DataSource, DataSink), f: &mut std::fmt::Formatter<'_>| {
            fmt_data_source(from, f, def_info)?;
            f.write_str(" -> ")?;
            match to {
                DataSink::Argument { function, arg_slot } => {
                    fmt_function(f, function.function, def_info)?;
                    write!(f, "({arg_slot})")
                }
                DataSink::Return => f.write_str("return"),
            }
        };
        let cutoff = 5;
        if !self.reached.is_empty() {
            write!(f, "  reached from: [")?;
            write_sep(f, ", ", self.reached.iter().take(cutoff), fmt_from_to)?;
            if self.reached.len() > cutoff {
                write!(f, ", ...")?;
            }
            writeln!(f, "]")?;
        }
        if !self.checkpointed.is_empty() {
            write!(f, "  checkpointed from: [")?;
            write_sep(f, ", ", self.checkpointed.iter().take(cutoff), fmt_from_to)?;
            if self.checkpointed.len() > cutoff {
                write!(f, ", ...")?;
            }
            writeln!(f, "]")?;
        }
        Ok(())
    }
}

fn path_to_str(info: &DefInfo) -> String {
    info.path
        .iter()
        .map(Identifier::as_str)
        .collect::<Vec<_>>()
        .join("::")
}

fn fmt_function(
    f: &mut std::fmt::Formatter<'_>,
    function: DefId,
    def_info: &HashMap<DefId, DefInfo>,
) -> std::fmt::Result {
    let info = &def_info[&function];
    let path = path_to_str(info);
    write!(f, "{}", path)
}

fn fmt_data_source(
    src: &DataSource,
    f: &mut std::fmt::Formatter<'_>,
    def_info: &HashMap<DefId, DefInfo>,
) -> std::fmt::Result {
    match src {
        DataSource::FunctionCall(fun) => fmt_function(f, fun.function, def_info),
        DataSource::Argument(num) => write!(f, "arg_{num}"),
    }
}

lazy_static::lazy_static! {
    static ref ALWAYS_HAPPENS_BEFORE_NAME: Identifier = Identifier::new_intern("always_happens_before");
}

impl<C> AlwaysHappensBefore<C> {
    /// Check this property holds and report it as diagnostics in the context.
    ///
    /// Additionally reports if the property was vacuous or had no starting
    /// nodes.
    pub fn report(&self, ctx: Arc<dyn HasDiagnosticsBase>) {
        let ctx = &CombinatorContext::new(*ALWAYS_HAPPENS_BEFORE_NAME, ctx);
        assert_warning!(ctx, self.started_with != 0, "Started with 0 nodes.");
        assert_warning!(ctx, !self.is_vacuous(), "Is vacuously true.");
        assert_error!(
            ctx,
            self.holds(),
            format!("Violation detected: {}", self.display(ctx))
        );
    }

    /// Returns `true` if the property that created these statistics holds.
    pub fn holds(&self) -> bool {
        self.reached.is_empty()
    }

    /// Fails if [`Self::holds`] is false.
    pub fn assert_holds(&self) -> Result<()> {
        ensure!(
            self.holds(),
            "AlwaysHappensBefore failed: found {} violating paths",
            self.reached.len()
        );
        Ok(())
    }

    /// `true` if this policy applied to no paths. E.g. either no starting nodes
    /// or no path from them can reach the terminal or the checkpoints (the
    /// graphs are disjoined).
    pub fn is_vacuous(&self) -> bool {
        self.checkpointed.is_empty() && self.reached.is_empty()
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

    let desc = ctx.desc();
    let controller = ctx.find_by_name("controller").unwrap();
    let ctrl = &desc.controllers[&controller];

    assert_eq!(ctx.marked_sinks(ctrl.data_sinks(), input).count(), 0);
    assert_eq!(ctx.marked_sinks(ctrl.data_sinks(), sink).count(), 2);
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
    ensure!(!pass.is_vacuous(), "{}", pass.display(ctx.clone()));

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
