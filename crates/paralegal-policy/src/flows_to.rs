use paralegal_spdg::{Ctrl, DataSink, DataSource, DataSourceIndex, DataSinkIndex, AnnotationMap};

use indexical::{impls::BitvecArcIndexMatrix as IndexMatrix, IndexedDomain, ToIndex};
use itertools::Itertools;

use std::{fmt, sync::Arc};

/// The transitive closure of the [`Ctrl::data_flow`] relation.
///
/// Implemented efficiently using an [`IndexedDomain`] over the
/// [`DataSource`] and [`DataSink`] types.
pub struct CtrlFlowsTo {
    /// The indexes of [`DataSource`]s in the controller.
    pub sources: Arc<IndexedDomain<DataSource>>,

    /// The indexes of [`DataSink`]s in the controller.
    pub sinks: Arc<IndexedDomain<DataSink>>,

    /// The transitive closure of the [`Ctrl::data_flow`] relation.
    ///
    /// See the [`IndexMatrix`] documentation for details on how to
    /// query this representation of the relation.
    pub data_flows_to: IndexMatrix<DataSourceIndex, DataSink>,

	/// The transitive closure of the [`Ctrl::ctrl_flow`] relation.
    pub ctrl_flows_to: IndexMatrix<DataSourceIndex, DataSink>,

	/// The transitive closure of the [`Ctrl::data_flow`] + [`Ctrl::ctrl_flow`] relation.
    pub flows_to: IndexMatrix<DataSourceIndex, DataSink>,
}

impl CtrlFlowsTo {
    /// Constructs the transitive closure from a [`Ctrl`].
    pub fn build(ctrl: &Ctrl) -> Self {
        // Collect all sources and sinks into indexed domains.
		let sources = Arc::new(IndexedDomain::from_iter(
			ctrl.all_sources().iter().map(|&s| s.clone())));
        let sinks = Arc::new(IndexedDomain::from_iter(
            ctrl.all_sinks().iter().map(|&s| s.clone()),
        ));

        // Connect each function-argument sink to its corresponding function sources.
        // This lets us compute the transitive closure by following through the `sink_to_source` map.
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

        // Initialize the `flows_to` relations with the data provided by `Ctrl::data_flow` and `Ctrl::ctrl_flow`.
        let mut data_flows_to = IndexMatrix::new(&sinks);
		let mut ctrl_flows_to = IndexMatrix::new(&sinks);
		let mut flows_to = IndexMatrix::new(&sinks);
        for (src, sinks) in &ctrl.data_flow.0 {
            let src = src.to_index(&sources);
            for sink in sinks {
                data_flows_to.insert(src, sink);
				flows_to.insert(src, sink);
            }
        }
        for (src, callsites) in &ctrl.ctrl_flow.0 {
            let src = src.to_index(&sources);
            for cs in callsites {
                ctrl_flows_to.insert(src, DataSink::Argument { function: cs.clone(), arg_slot: 0 });
				flows_to.insert(src, DataSink::Argument { function: cs.clone(), arg_slot: 0 });

				for (_, sink) in sinks.as_vec().iter_enumerated() {
					if let DataSink::Argument { function: arg_cs, .. } = sink {
						if arg_cs == cs {
							ctrl_flows_to.insert(src, sink);
							flows_to.insert(src, sink);
						}
					}
				}
            }
        }

		Self::iterate(&mut data_flows_to, &sources, &sink_to_source);
		Self::iterate(&mut ctrl_flows_to, &sources, &sink_to_source);
		Self::iterate(&mut flows_to, &sources, &sink_to_source);

        CtrlFlowsTo {
            sources,
            sinks,
            data_flows_to,
			ctrl_flows_to,
			flows_to
        }
    }

	fn iterate(flows_to: &mut IndexMatrix<DataSourceIndex, DataSink>, 
			sources: &Arc<IndexedDomain<DataSource>>, sink_to_source: &IndexMatrix<DataSinkIndex, DataSource>) {
		// Compute the transitive closure to a fixpoint.
        loop {
            let mut changed = false;

            for (src_idx, _src) in sources.as_vec().iter_enumerated() {
                for sink_idx in flows_to.row_set(&src_idx).indices().collect::<Vec<_>>() {
                    for trans_src_idx in sink_to_source.row_set(&sink_idx).indices() {
                        for trans_sink_idx in flows_to
                            .row_set(&trans_src_idx)
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
	}
}

impl fmt::Debug for CtrlFlowsTo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data_flows_to.fmt(f)
    }
}

#[test]
fn test_flows_to() {
    use paralegal_spdg::Identifier;
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx.find_by_name("controller").unwrap();
    let src = DataSource::Argument(0);
    let get_sink = |name| {
        let name = Identifier::new_intern(name);
        ctx.desc().controllers[&controller]
            .data_sinks()
            .find(|sink| match sink {
                DataSink::Argument { function, .. } => {
                    ctx.desc().def_info[&function.function].name == name
                }
                _ => false,
            })
            .unwrap()
    };
    let sink1 = get_sink("sink1");
    let sink2 = get_sink("sink2");
    assert!(ctx.flows_to(controller, &src, sink1));
    assert!(!ctx.flows_to(controller, &src, sink2));
}
