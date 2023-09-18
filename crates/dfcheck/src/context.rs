use std::{process::exit, io::Write};

use dfgraph::{
    Annotation, CallSite, Ctrl, DataSink, DataSource, HashMap, HashSet, Identifier,
    MarkerAnnotation, MarkerRefinement, ProgramDescription,
};

use anyhow::{anyhow, ensure, Result};
use indexical::ToIndex;
use itertools::Itertools;

use super::flows_to::CtrlFlowsTo;

use crate::diagnostics::{Diagnostics, Severity};

pub use crate::diagnostics::DiagnosticMessage;

/// User-defined PDG markers.
pub type Marker = Identifier;

type MarkerIndex = HashMap<Marker, Vec<(Identifier, MarkerRefinement)>>;
type FlowsTo = HashMap<Identifier, CtrlFlowsTo>;

/// Check the condition and emit a [`Context::error`] if it fails.
#[macro_export]
macro_rules! assert_error {
    ($ctx:expr, $cond: expr, $msg:expr) => {
        if $cond {
            $ctx.error($msg);
        }
    };
}

/// Check the condition and emit a [`Context::warning`] if it fails.
#[macro_export]
macro_rules! assert_warning {
    ($ctx:expr, $cond: expr, $msg:expr) => {
        if $cond {
            $ctx.warning($msg);
        }
    };
}

/// Data structures to be analyzed by user-defined properties.
#[derive(Debug)]
pub struct Context {
    marker_to_ids: MarkerIndex,
    desc: ProgramDescription,
    flows_to: FlowsTo,
    diagnostics: Diagnostics,
}

impl Context {
    /// Construct a [`Context`] from a [`ProgramDescription`].
    ///
    /// This also precomputes some data structures like an index over markers.
    pub fn new(desc: ProgramDescription) -> Self {
        Context {
            marker_to_ids: Self::build_index_on_markers(&desc),
            flows_to: Self::build_flows_to(&desc),
            desc,
            diagnostics: Default::default(),
        }
    }

    /// Dispatch and drain all queued diagnostics, aborts the program if any of
    /// them demand failure.
    pub fn emit_diagnostics(&self, w: impl Write) -> Result<()> {
        if !self.diagnostics.emit(w)? {
            exit(1)
        }
        Ok(())
    }

    /// Record a message to the user indicating a problem that will not cause
    /// verification to fail.
    pub fn warning(&self, msg: impl Into<DiagnosticMessage>) {
        self.diagnostics.record(msg, Severity::Warning)
    }

    /// Record a message to the user for a problem that will cause verification
    /// to fail.
    pub fn error(&self, msg: impl Into<DiagnosticMessage>) {
        self.diagnostics.record(msg, Severity::Fail)
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
    pub fn flows_to(&self, ctrl_id: Identifier, src: &DataSource, sink: &DataSink) -> bool {
        let ctrl_flows = &self.flows_to[&ctrl_id];
        ctrl_flows
            .flows_to
            .row_set(&src.to_index(&ctrl_flows.sources))
            .contains(sink)
    }

    /// Returns an iterator over all objects marked with `marker`.
    pub fn marked(
        &self,
        marker: Marker,
    ) -> impl Iterator<Item = &'_ (Identifier, MarkerRefinement)> + '_ {
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
        t: Identifier,
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
    pub fn otypes(&self, id: Identifier) -> Vec<Identifier> {
        let inner = || -> Option<_> {
            self.desc()
                .annotations
                .get(&id)?
                .0
                .iter()
                .filter_map(|annot| match annot {
                    Annotation::OType(ids) => Some(ids.clone()),
                    _ => None,
                })
                .next()
        };
        inner().unwrap_or_default()
    }

    /// Returns true if `id` identifies a function with name `name`.
    pub fn is_function(&self, id: Identifier, name: &str) -> bool {
        match id.as_str().rsplit_once('_') {
            Some((id_name, _)) => id_name == name,
            None => false,
        }
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
        ctrl: Identifier,
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
            .ok_or_else(|| anyhow!("Controller {ctrl} not found"))?
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
/// [`Self::found_any`]. Otherwise the information in this struct and its
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

impl AlwaysHappensBefore {
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
    assert!(ctx
        .marked(input)
        .any(|(id, _)| id.as_str().starts_with("Foo")));

    let desc = ctx.desc();
    let controller = desc
        .controllers
        .keys()
        .find(|id| ctx.is_function(**id, "controller"))
        .unwrap();
    let ctrl = &desc.controllers[controller];

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
        ctrl_name: Identifier,
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

    let ctrl_name = *desc
        .controllers
        .keys()
        .find(|id| ctx.is_function(**id, "happens_before_pass"))
        .unwrap();

    let pass = ctx.always_happens_before(
        ctrl_name,
        marked_sources(desc, ctrl_name, Identifier::new_intern("start")).cloned(),
        |checkpoint| is_checkpoint(desc, checkpoint),
        is_terminal,
    )?;

    ensure!(pass.holds());
    ensure!(!pass.is_vacuous(), "{pass}");

    let ctrl_name = *desc
        .controllers
        .keys()
        .find(|id| ctx.is_function(**id, "happens_before_fail"))
        .unwrap();

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
