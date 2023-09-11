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

pub struct Context {
    pub marker_to_ids: MarkerIndex,
    desc: ProgramDescription,
    flows_to: FlowsTo,
}

impl Context {
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

    pub fn flows_to(&self, ctrl_id: &Identifier, src: &DataSource, sink: &DataSink) -> bool {
        let ctrl_flows = &self.flows_to[ctrl_id];
        ctrl_flows
            .flows_to
            .row_set(&src.to_index(&ctrl_flows.sources))
            .contains(sink)
    }

    pub fn marked(
        &self,
        marker: Marker,
    ) -> impl Iterator<Item = &'_ (Identifier, MarkerRefinement)> + '_ {
        self.marker_to_ids
            .get(&marker)
            .into_iter()
            .flat_map(|v| v.iter())
    }

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

    pub fn desc(&self) -> &ProgramDescription {
        &self.desc
    }

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
}
