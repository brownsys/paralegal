use crate::desc::{Ctrl, DataSink, DataSinkDomain, DataSource, DataSourceDomain, DataSourceIndex};

use flowistry::indexed::{IndexMatrix, IndexedDomain, ToIndex};

use itertools::Itertools;

use std::rc::Rc;

pub struct CtrlFlowsTo {
    pub sources: Rc<DataSourceDomain>,
    pub sinks: Rc<DataSinkDomain>,
    pub flows_to: IndexMatrix<DataSourceIndex, DataSink>,
}

impl CtrlFlowsTo {
    pub fn build(ctrl: &Ctrl) -> Self {
        let sources = Rc::new(DataSourceDomain::new(
            ctrl.data_flow.0.keys().cloned().collect(),
        ));
        let sinks = Rc::new(DataSinkDomain::new(
            ctrl.data_flow
                .0
                .values()
                .flatten()
                .dedup()
                .cloned()
                .collect(),
        ));
        let mut sink_to_source = IndexMatrix::new(&sources);
        for (sink_idx, sink) in sinks.as_vec().iter_enumerated() {
            for (src_idx, src) in sources.as_vec().iter_enumerated() {
                if let (DataSource::FunctionCall(f1), DataSink::Argument { function: f2, .. }) =
                    (src, sink)
                {
                    if f1 == f2 {
                        sink_to_source.insert(sink_idx, src_idx);
                    }
                }
            }
        }

        let mut flows_to = IndexMatrix::new(&sinks);

        for (src, sinks) in &ctrl.data_flow.0 {
            let src = src.to_index(&sources);
            for sink in sinks {
                flows_to.insert(src, sink);
            }
        }

        loop {
            let mut changed = false;

            for (src_idx, _src) in sources.as_vec().iter_enumerated() {
                for sink_idx in flows_to.row_set(src_idx).indices().collect::<Vec<_>>() {
                    for trans_src_idx in sink_to_source.row_set(sink_idx).indices() {
                        for trans_sink_idx in flows_to
                            .row_set(trans_src_idx)
                            .indices()
                            .collect::<Vec<_>>()
                        {
                            changed |= flows_to.insert(src_idx, trans_sink_idx);
                        }
                    }
                }
            }

            if !changed {
                break;
            }
        }

        CtrlFlowsTo {
            sources,
            sinks,
            flows_to,
        }
    }
}
