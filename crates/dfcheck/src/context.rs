use dfgraph::{
    Annotation, CallSite, Ctrl, DataSink, DataSource, HashMap, HashSet, Identifier,
    MarkerAnnotation, MarkerRefinement, ProgramDescription,
};

use anyhow::{anyhow, ensure, Result};
use indexical::ToIndex;
use itertools::Itertools;

use super::flows_to::CtrlFlowsTo;

/// User-defined PDG markers.
pub type Marker = Identifier;

type MarkerIndex = HashMap<Marker, Vec<(Identifier, MarkerRefinement)>>;
type FlowsTo = HashMap<Identifier, CtrlFlowsTo>;

/// Data structures to be analyzed by user-defined properties.
#[derive(Debug)]
pub struct Context {
    marker_to_ids: MarkerIndex,
    desc: ProgramDescription,
    flows_to: FlowsTo,
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
        }
    }

    fn build_index_on_markers(desc: &ProgramDescription) -> MarkerIndex {
        desc.annotations
            .iter()
            .flat_map(|(id, (annots, _))| {
                annots.iter().filter_map(move |annot| match annot {
                    Annotation::Label(MarkerAnnotation { marker, refinement }) => {
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
    pub fn flows_to(&self, ctrl_id: &Identifier, src: &DataSource, sink: &DataSink) -> bool {
        let ctrl_flows = &self.flows_to[ctrl_id];
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
        t: &'a Identifier,
    ) -> impl Iterator<Item = &'a DataSource> + 'a {
        c.types
            .0
            .iter()
            .filter_map(move |(src, ids)| ids.contains(t).then_some(src))
    }

    /// Returns the input [`ProgramDescription`].
    pub fn desc(&self) -> &ProgramDescription {
        &self.desc
    }

    /// Returns all the [`Annotation::OType`]s for a controller `id`.
    pub fn otypes(&self, id: &Identifier) -> Vec<Identifier> {
        let inner = || -> Option<_> {
            self.desc()
                .annotations
                .get(id)?
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
        match id.as_str().split_once('_') {
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
    pub fn always_happens_before(
        &self,
        ctrl: Identifier,
        starting_points: impl Iterator<Item = DataSource>,
        mut is_checkpoint: impl FnMut(&DataSink) -> bool,
        mut is_terminal: impl FnMut(&DataSink) -> bool,
    ) -> Result<AlwaysHappensBefore> {
        let mut seen = HashSet::<&DataSink>::new();
        let mut num_seen = 0;
        let mut num_violated = 0;

        let mut queue = starting_points
            .zip(std::iter::repeat(true))
            .collect::<Vec<_>>();

        let started_with = queue.len();

        while let Some((current, mut is_violated)) = queue.pop() {
            for sink in self
                .desc()
                .controllers
                .get(&ctrl)
                .ok_or_else(|| anyhow!("Controller {ctrl} not found"))?
                .data_flow
                .0
                .get(&current)
                .into_iter()
                .flatten()
            {
                if is_checkpoint(sink) {
                    is_violated = false;
                }
                match sink {
                    _ if is_terminal(sink) => {
                        num_seen += 1;
                        if is_violated {
                            num_violated += 1;
                        }
                    }
                    DataSink::Return => {
                        num_seen += 1;
                        if is_violated {
                            num_violated += 1;
                        }
                    }
                    DataSink::Argument {
                        function,
                        arg_slot: _,
                    } => {
                        if seen.insert(sink) {
                            queue.push((DataSource::FunctionCall(function.clone()), is_violated));
                        }
                    }
                }
            }
        }

        Ok(AlwaysHappensBefore {
            num_seen,
            num_violated,
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
/// The stable API of this struct is [`Self::holds`], [`Self::assert_holds`] and
/// [`Self::found_any`]. Otherwise the information in this struct and its
/// printed representations should be considered unstable and
/// for-human-eyes-only.
pub struct AlwaysHappensBefore {
    /// How many paths terminated in `is_terminal`.
    num_seen: i32,
    /// How many terminating paths violated the property.
    num_violated: i32,
    /// How large was the set of initial nodes this traversal started with.
    started_with: usize,
}

impl std::fmt::Display for AlwaysHappensBefore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            num_seen,
            num_violated,
            started_with,
        } = self;
        write!(
            f,
            "Saw {num_seen} paths, {num_violated} violations, started with {started_with} nodes"
        )
    }
}

impl AlwaysHappensBefore {
    /// Returns `true` if the property that created these statistics holds.
    pub fn holds(&self) -> bool {
        self.num_violated == 0
    }

    /// Fails if [`Self::holds`] is false.
    pub fn assert_holds(&self) -> Result<()> {
        ensure!(
            self.holds(),
            "AlwaysHappensBefore failed: found {} violating paths",
            self.num_violated
        );
        Ok(())
    }

    /// Were any paths covered by this policy?
    pub fn is_vacuous(&self) -> bool {
        self.num_seen != 0
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
