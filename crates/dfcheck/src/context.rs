use dfgraph::{
    Annotation, CallSite, Ctrl, DataSink, DataSource, HashMap, Identifier, MarkerAnnotation,
    MarkerRefinement, ProgramDescription, Symbol,
};

use flowistry::indexed::ToIndex;
use itertools::Itertools;

use super::flows_to::CtrlFlowsTo;

pub type Label = Symbol;
pub type LabelIndex = HashMap<Label, Vec<(Identifier, MarkerRefinement)>>;
pub type FlowsTo = HashMap<Identifier, CtrlFlowsTo>;

pub struct Context {
    label_to_ids: LabelIndex,
    desc: ProgramDescription,
    flows_to: FlowsTo,
}

impl Context {
    pub fn new(desc: ProgramDescription) -> Self {
        Context {
            label_to_ids: Self::build_index_on_labels(&desc),
            flows_to: Self::build_flows_to(&desc),
            desc,
        }
    }

    fn build_index_on_labels(desc: &ProgramDescription) -> LabelIndex {
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
            .row_set(src.to_index(&ctrl_flows.sources))
            .contains(sink)
    }

    pub fn labelled(
        &self,
        label: Label,
    ) -> impl Iterator<Item = &'_ (Identifier, MarkerRefinement)> + '_ {
        self.label_to_ids
            .get(&label)
            .into_iter()
            .flat_map(|v| v.iter())
    }

    pub fn labeled_sinks<'a>(
        &'a self,
        dsts: impl IntoIterator<Item = &'a DataSink> + 'a,
        label: Label,
    ) -> impl Iterator<Item = &'a DataSink> + 'a {
        dsts.into_iter().filter(move |dst| match dst {
            DataSink::Argument { function, arg_slot } => self
                .label_to_ids
                .get(&label)
                .map(|labels| {
                    labels.iter().any(|(id, refinement)| {
                        id == &function.function
                            && (refinement.on_self()
                                || refinement.on_argument().contains(*arg_slot as u32).unwrap())
                    })
                })
                .unwrap_or(false),
            _ => false,
        })
    }

    pub fn labeled_callsites<'a>(
        &'a self,
        dsts: impl IntoIterator<Item = &'a DataSink> + 'a,
        label: Label,
    ) -> impl Iterator<Item = &'a CallSite> + 'a {
        self.labeled_sinks(dsts, label)
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
            .unwrap_or_else(|| Vec::new())
    }
}
