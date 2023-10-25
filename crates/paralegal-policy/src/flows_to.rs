use paralegal_spdg::{
    CallSiteOrDataSink, CallSiteOrDataSinkIndex, Ctrl, DataSink, DataSource, DataSourceIndex,
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

    /// Mapping from [`CallSiteOrDataSink::CallSite`]s to the [`CallSiteOrDataSink::DataSink(CallArgument)`]s that they are related to.
    pub callsites_to_callargs: IndexMatrix<CallSiteOrDataSinkIndex, CallSiteOrDataSink>,

    /// The transitive closure of the [`Ctrl::data_flow`] relation.
    /// If a source flows to a [`DataSink::Argument`], it also flows into its CallSite.
    ///
    /// See the [`IndexMatrix`] documentation for details on how to
    /// query this representation of the relation.
    pub data_flows_to: IndexMatrix<DataSourceIndex, CallSiteOrDataSink>,

    /// The transitive closure of the [`Ctrl::data_flow`] and [`Ctrl::ctrl_flow`] relations representing mixed flows of data and control.
    /// If a source data-flows to a [`DataSink::Argument`], it flows into its CallSite.
    /// If a source control-flows into a CallSite, it also flows into all of the [`DataSink::Argument`]s related to it.
    pub flows_to: IndexMatrix<DataSourceIndex, CallSiteOrDataSink>,
}

impl CtrlFlowsTo {
    /// Constructs the transitive closure from a [`Ctrl`].
    pub fn build(ctrl: &Ctrl) -> Self {
        // Collect all sources and sinks into indexed domains.
        let sources = Arc::new(IndexedDomain::from_iter(ctrl.all_sources().cloned()));
        let sinks = Arc::new(IndexedDomain::from_iter(ctrl.all_call_sites_or_sinks()));

        // Connect each function-argument sink to its corresponding function sources.
        // This lets us compute the transitive closure by following through the `sink_to_source` map.
        let mut sink_to_source = IndexMatrix::new(&sources);
        for (sink_idx, sink) in sinks.as_vec().iter_enumerated() {
            let src = match sink {
                CallSiteOrDataSink::DataSink(DataSink::Argument { function: f, .. }) => {
                    DataSource::FunctionCall(f.clone())
                }
                CallSiteOrDataSink::CallSite(f) => DataSource::FunctionCall(f.clone()),
                _ => continue,
            };
            let src_idx = if sources.contains(&src) {
                sources.index(&src)
            } else {
                continue;
            };
            sink_to_source.insert(sink_idx, src_idx);
        }

        /// Compute the `flows_to` transitive closure to a fixpoint.
        fn iterate(
            sources: &Arc<IndexedDomain<DataSource>>,
            flows_to: &mut IndexMatrix<DataSourceIndex, CallSiteOrDataSink>,
            sink_to_source: &IndexMatrix<CallSiteOrDataSinkIndex, DataSource>,
        ) {
            let mut changed = true;
            while changed {
                changed = false;
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
        let mut callsites_to_callargs = IndexMatrix::new(&sinks);
        for (callsite_idx, callsite) in sinks.as_vec().iter_enumerated() {
            for (sink_idx, sink) in sinks.as_vec().iter_enumerated() {
                if let (
                    CallSiteOrDataSink::DataSink(DataSink::Argument { function: f1, .. }),
                    CallSiteOrDataSink::CallSite(f2),
                ) = (sink, callsite)
                {
                    if f1 == f2 {
                        callsites_to_callargs.insert(callsite_idx, sink_idx);
                    }
                }
            }
        }
        // Initialize the `flows_to` relation with the data provided by `Ctrl::ctrl_flow`.
        for (src, callsites) in &ctrl.ctrl_flow.0 {
            let src = src.to_index(&sources);
            for cs in callsites {
                let new_call_site: CallSiteOrDataSink = cs.clone().into();
                flows_to.insert(src, &new_call_site);
                // initialize with flows from the DataSource to all of the CallSite's DataSinks
                for sink in callsites_to_callargs
                    .row_set(&sinks.index(&new_call_site))
                    .iter()
                {
                    flows_to.insert(src, sink);
                }
            }
        }

        iterate(&sources, &mut flows_to, &sink_to_source);

        CtrlFlowsTo {
            sources,
            sinks,
            callsites_to_callargs,
            data_flows_to,
            flows_to,
        }
    }
}

impl fmt::Debug for CtrlFlowsTo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CtrlFlowsTo")
            .field("flows_to", &self.flows_to)
            .field("data_flows_to", &self.data_flows_to)
            .finish()
    }
}

#[test]
fn test_data_flows_to() {
    use paralegal_spdg::Identifier;
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx.find_by_name("controller").unwrap();
    let src = crate::Node {
        ctrl_id: controller,
        typ: (&DataSource::Argument(0)).into(),
    };
    let get_sink_node = |name| {
        let name = Identifier::new_intern(name);
        let node = ctx.desc().controllers[&controller]
            .data_sinks()
            .find(|sink| match sink {
                DataSink::Argument { function, .. } => {
                    ctx.desc().def_info[&function.function].name == name
                }
                _ => false,
            })
            .unwrap();
        crate::Node {
            ctrl_id: controller,
            typ: node.into(),
        }
    };
    let sink1 = get_sink_node("sink1");
    let sink2 = get_sink_node("sink2");
    assert!(ctx.flows_to(src, sink1, crate::EdgeType::Data));
    assert!(!ctx.flows_to(src, sink2, crate::EdgeType::Data));
}

#[test]
fn test_ctrl_flows_to() {
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx.find_by_name("controller_ctrl").unwrap();
    let src_a = crate::Node {
        ctrl_id: controller,
        typ: (&DataSource::Argument(0)).into(),
    };
    let src_b = crate::Node {
        ctrl_id: controller,
        typ: (&DataSource::Argument(1)).into(),
    };
    let src_c = crate::Node {
        ctrl_id: controller,
        typ: (&DataSource::Argument(2)).into(),
    };
    let cs1 = crate::test_utils::get_callsite_node(ctx, controller, "sink1");
    let cs2 = crate::test_utils::get_callsite_node(ctx, controller, "sink2");
    assert!(ctx.flows_to(src_a, cs1, crate::EdgeType::Control));
    assert!(ctx.flows_to(src_c, cs2, crate::EdgeType::Control));
    assert!(ctx.flows_to(src_a, cs2, crate::EdgeType::Control));
    assert!(!ctx.flows_to(src_b, cs1, crate::EdgeType::Control));
    assert!(!ctx.flows_to(src_b, cs2, crate::EdgeType::Control));
}

#[test]
fn test_flows_to() {
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx.find_by_name("controller_data_ctrl").unwrap();
    let src_a = crate::Node {
        ctrl_id: controller,
        typ: (&DataSource::Argument(0)).into(),
    };
    let src_b = crate::Node {
        ctrl_id: controller,
        typ: (&DataSource::Argument(1)).into(),
    };
    let sink = crate::test_utils::get_sink_node(ctx, controller, "sink1");
    let cs = crate::test_utils::get_callsite_node(ctx, controller, "sink1");
    // a flows to the sink1 callsite (by ctrl flow)
    assert!(ctx.flows_to(src_a, cs, crate::EdgeType::DataAndControl));
    assert!(!ctx.flows_to(src_a, cs, crate::EdgeType::Data));
    // b flows to the sink1 datasink (by data flow)
    assert!(ctx.flows_to(src_b, sink, crate::EdgeType::DataAndControl));
    assert!(ctx.flows_to(src_b, sink, crate::EdgeType::Data));
}
