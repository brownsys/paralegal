use paralegal_spdg::{CallSiteOrDataSink, CallSiteOrDataSinkIndex, Ctrl, DataSink, DataSource,
    DataSourceIndex,
};

use indexical::{impls::BitvecArcIndexMatrix as IndexMatrix, IndexedDomain, ToIndex};

use std::{fmt, sync::Arc};

/// The transitive closure of the [`Ctrl::data_flow`] relation.
///
/// Implemented efficiently using an [`IndexedDomain`] over the
/// [`DataSource`] and [`DataSink`] types.
pub struct CtrlFlowsTo {
    /// The indexes of [`DataSource`]s in the controller.
    pub sources: Arc<IndexedDomain<DataSource>>,

    /// The indexes of [`CallSiteOrDataSink`]s in the controller.
    pub sinks: Arc<IndexedDomain<CallSiteOrDataSink>>,

    /// The transitive closure of the [`Ctrl::data_flow`] relation.
    /// If a source flows to a [`DataSink::Argument`], it also flows into its [`CallSite`].
    ///
    /// See the [`IndexMatrix`] documentation for details on how to
    /// query this representation of the relation.
    pub data_flows_to: IndexMatrix<DataSourceIndex, CallSiteOrDataSink>,

    /// The transitive closure of the [`Ctrl::data_flow`] and [`Ctrl::ctrl_flow`] relations. 
	/// If a source data-flows to a [`DataSink::Argument`], it flows into its [`CallSite`].
	/// If a source control-flows into a [`CallSite`], it also flows into all of the [`DataSink::Argument`]s related to it.
    pub flows_to: IndexMatrix<DataSourceIndex, CallSiteOrDataSink>,
}

impl CtrlFlowsTo {
    /// Constructs the transitive closure from a [`Ctrl`].
    pub fn build(ctrl: &Ctrl) -> Self {
        // Collect all sources and sinks into indexed domains.
        let sources = Arc::new(IndexedDomain::from_iter(
            ctrl.all_sources().iter().map(|&s| s.clone()),
        ));
        let sinks = Arc::new(IndexedDomain::from_iter(ctrl.all_call_sites_or_sinks()));

        // Connect each function-argument sink to its corresponding function sources.
        // This lets us compute the transitive closure by following through the `sink_to_source` map.
        let mut sink_to_source = IndexMatrix::new(&sources);
        for (sink_idx, sink) in sinks.as_vec().iter_enumerated() {
            for (src_idx, src) in sources.as_vec().iter_enumerated() {
                if let (
                    DataSource::FunctionCall(f1),
                    CallSiteOrDataSink::DataSink(DataSink::Argument { function: f2, .. }),
                ) = (src, sink)
                {
                    if f1 == f2 {
                        sink_to_source.insert(sink_idx, src_idx);
                    }
                } else if let (DataSource::FunctionCall(f1), CallSiteOrDataSink::CallSite(f2)) =
                    (src, sink)
                {
                    if f1 == f2 {
                        sink_to_source.insert(sink_idx, src_idx);
                    }
                }
            }
        }

        fn iterate(
            sources: &Arc<IndexedDomain<DataSource>>,
            flows_to: &mut IndexMatrix<DataSourceIndex, CallSiteOrDataSink>,
            sink_to_source: &IndexMatrix<CallSiteOrDataSinkIndex, DataSource>,
        ) {
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

        // Initialize the `flows_to` relation with the data provided by `Ctrl::data_flow`.
        let mut data_flows_to = IndexMatrix::new(&sinks);
        for (src, sinks) in &ctrl.data_flow.0 {
            let src = src.to_index(&sources);
            for sink in sinks {
                data_flows_to.insert(src, CallSiteOrDataSink::DataSink(sink.clone()));
                // initialize with flows from DataSource to the DataSink's CallSite
                if let DataSink::Argument { function, .. } = sink {
                    data_flows_to.insert(src, CallSiteOrDataSink::CallSite(function.clone()));
                }
            }
        }

        iterate(&sources, &mut data_flows_to, &sink_to_source);

        // Initialize the `flows_to` relation with the data provided by `Ctrl::data_flow`.
        let mut flows_to = data_flows_to.clone();

        // Connect each callsite to its function-argument sinks
        let mut cs_to_sink = IndexMatrix::new(&sinks);
        for (callsite_idx, callsite) in sinks.as_vec().iter_enumerated() {
            for (sink_idx, sink) in sinks.as_vec().iter_enumerated() {
                if let (
                    CallSiteOrDataSink::DataSink(DataSink::Argument { function: f1, .. }),
                    CallSiteOrDataSink::CallSite(f2),
                ) = (sink, callsite)
                {
                    if f1 == f2 {
                        cs_to_sink.insert(callsite_idx, sink_idx);
                    }
                }
            }
        }
        // Initialize the `flows_to` relation with the data provided by `Ctrl::ctrl_flow`.
        for (src, callsites) in &ctrl.ctrl_flow.0 {
            let src = src.to_index(&sources);
            for cs in callsites {
                let new_call_site = CallSiteOrDataSink::CallSite(cs.clone());
                flows_to.insert(src, &new_call_site);
                // initialize with flows from the DataSource to all of the CallSite's DataSinks
                for sink in cs_to_sink.row_set(&sinks.index(&new_call_site)).iter() {
                    flows_to.insert(src, sink);
                }
            }
        }

        iterate(&sources, &mut flows_to, &sink_to_source);

        CtrlFlowsTo {
            sources,
            sinks,
            data_flows_to,
            flows_to,
        }
    }
}

impl fmt::Debug for CtrlFlowsTo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data_flows_to.fmt(f)
    }
}

#[test]
fn test_data_flows_to() {
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
    assert!(ctx.data_flows_to(controller, &src, sink1));
    assert!(!ctx.data_flows_to(controller, &src, sink2));
}

#[test]
fn test_flows_to() {
    use paralegal_spdg::Identifier;
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx.find_by_name("controller_data_ctrl").unwrap();
    let src_a = DataSource::Argument(0);
    let src_b = DataSource::Argument(1);
    let get_datasink = |name| {
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

    let get_callsite = |name| {
        let name = Identifier::new_intern(name);
        ctx.desc().controllers[&controller]
            .call_sites()
            .find(|callsite| ctx.desc().def_info[&callsite.function].name == name)
            .unwrap()
    };
    let sink = CallSiteOrDataSink::DataSink(get_datasink("sink1").clone());
    let cs = CallSiteOrDataSink::CallSite(get_callsite("sink1").clone());
    // a flows to the sink1 callsite (by ctrl flow)
    assert!(ctx.flows_to(controller, &src_a, &cs));
    // b flows to the sink1 datasink (by data flow)
    assert!(ctx.flows_to(controller, &src_b, &sink));
}
