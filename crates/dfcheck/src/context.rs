use dfgraph::{
    Annotation, CallSite, Ctrl, DataSink, DataSource, HashMap, Identifier, MarkerAnnotation,
    MarkerRefinement, ProgramDescription,
};

use indexical::ToIndex;
use itertools::Itertools;

use super::flows_to::CtrlFlowsTo;

pub type Marker = Identifier;
pub type MarkerIndex = HashMap<Marker, Vec<(Identifier, MarkerRefinement)>>;
pub type FlowsTo = HashMap<Identifier, CtrlFlowsTo>;

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
        self.desc().annotations[id]
            .0
            .iter()
            .filter_map(|annot| match annot {
                Annotation::OType(ids) => Some(ids.clone()),
                _ => None,
            })
            .next()
            .unwrap_or_default()
    }

    /// Returns true if `id` identifies a function with name `name`.
    pub fn is_function(&self, id: Identifier, name: &str) -> bool {
        match id.as_str().split_once('_') {
            Some((id_name, _)) => id_name == name,
            None => false,
        }
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
