use itertools::Itertools;
use paralegal_spdg::{
    CallSiteOrDataSink, CallSiteOrDataSinkIndex, Ctrl, DataSink, DataSource, DataSourceIndex,
    ProgramDescription,
};

use indexical::{impls::BitvecArcIndexMatrix as IndexMatrix, IndexedDomain, ToIndex};

use std::{fmt, sync::Arc};

use crate::NodeType;

/// The transitive closure of the [`Ctrl::data_flow`] relation.
///
/// Implemented efficiently using an [`IndexedDomain`] over the
/// [`DataSource`] and [`CallSiteOrDataSink`] types.
///
/// ## Relationship of [`CtrlFlowsTo::data_flows_to`], [`CtrlFlowsTo::data_and_control_flows_to()`], [`crate::Context::flows_to()`], [`crate::Context::influencers()`] and [`crate::Context::influencees()`]
///
/// - Indexes in [`CtrlFlowsTo`] vs functions in [`crate::Context`]: the indexes are
/// used for efficiency when computing the functions in [`crate::Context`]. However, they
/// are from [`DataSource`] to [`CallSiteOrDataSink`], so do not provide all of the
///  information that is needed answer questions about any kind of [`crate::Node`] and any
/// kind of [`crate::EdgeType`] in an intuitive way.
///
/// - [`CtrlFlowsTo::data_flows_to`] vs [`CtrlFlowsTo::data_and_control_flows_to()`]: Both
///  return the transitive closure of relations in the controller:
/// both use the [`Ctrl::data_flow`] relation, and [`CtrlFlowsTo::data_and_control_flows_to()`]
/// additionally includes relations from [`Ctrl::ctrl_flow`].
///
/// - [`crate::Context::flows_to()`], [`crate::Context::influencers()`] and
/// [`crate::Context::influencees()`] work for any kind of node as their srcs or sinks.
///
///     - [`NodeType::ControllerArgument`] cannot act as a sink
/// ([`crate::Context::flows_to()`] will always return false with it as the sink argument
/// and [`crate::Context::influencers()`] will be empty).
///
///     - [`NodeType::Return`] cannot act as a src ([`crate::Context::flows_to()`]
///  will always return false with it as the src argument and
/// [`crate::Context::influencees()`] will be empty).
///
///     - For all other node type combinations, the src node will be
/// translated to its respective [`DataSource`] (i.e. for a
/// [`NodeType::CallArgument`], the [`DataSource::FunctionCall`] will be used) and
/// the sink node will be translated to its respective [`CallSiteOrDataSink`] and
///  the correct index will be queried. Additionally, we also special-case
/// relationships between [`NodeType::CallArgument`] and [`NodeType::CallSite`] to
/// capture the data-flow between them, which would otherwise be lost through the
/// aforementioned procedure.
///
///     - For [`crate::Context::influencers()`] and
/// [`crate::Context::influencees()`], querying the indexes does not exhaustively
/// return all type of [`crate::Node`]s since they only provide either [`DataSource`]
/// influencers or [`CallSiteOrDataSink`] influencees.
/// So, these functions add the [`NodeType::CallArgument`]s related to each
/// [`NodeType::CallSite`] and the [`NodeType::CallSite`] related to each
/// [`NodeType::CallArgument`] respectively.
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
}

impl CtrlFlowsTo {
    /// Constructs the transitive closure from a [`Ctrl`].
    pub fn build(ctrl: &Ctrl) -> Self {
        // Collect all sources and sinks into indexed domains.
        let sources = Arc::new(IndexedDomain::from_iter(ctrl.all_sources().cloned().chain(
            ctrl.all_call_sites_or_sinks().filter_map(|cs_or_ds| {
                let nt: NodeType = cs_or_ds.into();
                nt.as_data_source()
            }),
        )));
        let sinks = Arc::new(IndexedDomain::from_iter(
            ctrl.all_call_sites_or_sinks()
                .chain(ctrl.all_sources().filter_map(|src| {
                    let nt: NodeType = src.clone().into();
                    nt.as_call_site_or_data_sink()
                })),
        ));

        // Connect each function-argument sink to its corresponding function sources.
        // This lets us compute the transitive closure by following through the `sink_to_source` map.
        let mut sink_to_source = IndexMatrix::new(&sources);
        for (sink_idx, sink) in sinks.as_vec().iter_enumerated() {
            let src = match sink {
                CallSiteOrDataSink::DataSink(DataSink::Argument { function: f, .. }) => {
                    DataSource::FunctionCall(*f)
                }
                CallSiteOrDataSink::CallSite(f) => DataSource::FunctionCall(*f),
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
                data_flows_to.insert(src, CallSiteOrDataSink::DataSink(*sink));
                // initialize with flows from DataSource to the DataSink's CallSite
                if let DataSink::Argument { function, .. } = sink {
                    data_flows_to.insert(src, CallSiteOrDataSink::CallSite(*function));
                }
            }
        }

        iterate(&sources, &mut data_flows_to, &sink_to_source);

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

        CtrlFlowsTo {
            sources,
            sinks,
            callsites_to_callargs,
            data_flows_to,
        }
    }

    /// Returns whether src->sink is in the transitive closure of data and control flow.
    pub fn data_and_control_flows_to(
        &self,
        ctrl: &Ctrl,
        src: DataSource,
        sink: CallSiteOrDataSink,
    ) -> bool {
        let mut influencees = DataAndControlInfluencees::new(src, ctrl, self);
        influencees.contains(&sink)
    }
}

pub(crate) struct DataAndControlInfluencees<'a> {
    to_return: Vec<CallSiteOrDataSink>,
    queue: Vec<DataSource>,
    seen: std::collections::HashSet<CallSiteOrDataSink>,
    ctrl: &'a Ctrl,
    flows_to: &'a CtrlFlowsTo,
}

impl<'a> DataAndControlInfluencees<'a> {
    pub(crate) fn new(src: DataSource, ctrl: &'a Ctrl, flows_to: &'a CtrlFlowsTo) -> Self {
        let queue = vec![src];
        let seen = std::collections::HashSet::<CallSiteOrDataSink>::new();

        DataAndControlInfluencees {
            to_return: Vec::new(),
            queue,
            seen,
            ctrl,
            flows_to,
        }
    }
}

impl<'a> Iterator for DataAndControlInfluencees<'a> {
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(r) = self.to_return.pop() {
            return Some(r);
        }
        if let Some(cur_src) = self.queue.pop() {
            let cur_src_index = cur_src.clone().to_index(&self.flows_to.sources);
            for cur_sink in self.flows_to.data_flows_to.row_set(&cur_src_index).iter() {
                self.to_return.push(cur_sink.clone());

                let cur_sink_callsite = match &cur_sink {
                    CallSiteOrDataSink::CallSite(cs) => cs,
                    CallSiteOrDataSink::DataSink(DataSink::Argument { function, .. }) => function,
                    _ => continue,
                };
                if self.seen.insert(cur_sink.clone()) {
                    self.queue.push(cur_sink_callsite.clone().into());
                }
            }

            if let Some(callsites) = self.ctrl.ctrl_flow.get(&cur_src) {
                for cur_cs_sink in callsites {
                    let cs_or_ds: CallSiteOrDataSink = cur_cs_sink.clone().into();
                    self.to_return.push(cs_or_ds.clone());
                    for arg in self
                        .flows_to
                        .callsites_to_callargs
                        .row(&cs_or_ds.clone().to_index(&self.flows_to.sinks))
                    {
                        self.to_return.push(arg.clone());
                    }

                    if self.seen.insert(cs_or_ds) {
                        self.queue.push((cur_cs_sink.clone()).into());
                    }
                }
            }
        }
        if let Some(r) = self.to_return.pop() {
            return Some(r);
        }
        None
    }

    type Item = CallSiteOrDataSink;
}

impl fmt::Debug for CtrlFlowsTo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CtrlFlowsTo")
            .field("data_flows_to", &self.data_flows_to)
            .finish()
    }
}

#[test]
fn test_data_flows_to() {
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx.find_by_name("controller").unwrap();
    let src = crate::Node {
        ctrl_id: controller,
        typ: DataSource::Argument(0).into(),
    };
    let sink1 = crate::test_utils::get_sink_node(&ctx, controller, "sink1").unwrap();
    let sink2 = crate::test_utils::get_sink_node(&ctx, controller, "sink2").unwrap();
    assert!(ctx.flows_to(src, sink1, crate::EdgeType::Data));
    assert!(!ctx.flows_to(src, sink2, crate::EdgeType::Data));
}

#[test]
fn test_ctrl_flows_to() {
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx.find_by_name("controller_ctrl").unwrap();
    let src_a = crate::Node {
        ctrl_id: controller,
        typ: DataSource::Argument(0).into(),
    };
    let src_b = crate::Node {
        ctrl_id: controller,
        typ: DataSource::Argument(1).into(),
    };
    let src_c = crate::Node {
        ctrl_id: controller,
        typ: DataSource::Argument(2).into(),
    };
    let cs1 = crate::test_utils::get_callsite_node(&ctx, controller, "sink1").unwrap();
    let cs2 = crate::test_utils::get_callsite_node(&ctx, controller, "sink2").unwrap();
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
        typ: DataSource::Argument(0).into(),
    };
    let src_b = crate::Node {
        ctrl_id: controller,
        typ: DataSource::Argument(1).into(),
    };
    let sink = crate::test_utils::get_sink_node(&ctx, controller, "sink1").unwrap();
    let cs = crate::test_utils::get_callsite_node(&ctx, controller, "sink1").unwrap();
    // a flows to the sink1 callsite (by ctrl flow)
    assert!(ctx.flows_to(src_a, cs, crate::EdgeType::DataAndControl));
    assert!(!ctx.flows_to(src_a, cs, crate::EdgeType::Data));
    // b flows to the sink1 datasink (by data flow)
    assert!(ctx.flows_to(src_b, sink, crate::EdgeType::DataAndControl));
    assert!(ctx.flows_to(src_b, sink, crate::EdgeType::Data));
}

#[test]
fn test_args_flow_to_cs() {
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx.find_by_name("controller_data_ctrl").unwrap();
    let sink = crate::test_utils::get_sink_node(&ctx, controller, "sink1").unwrap();
    let cs = crate::test_utils::get_callsite_node(&ctx, controller, "sink1").unwrap();

    assert!(ctx.flows_to(sink, cs, crate::EdgeType::Data));
    assert!(ctx.flows_to(sink, cs, crate::EdgeType::DataAndControl));
    assert!(!ctx.flows_to(sink, cs, crate::EdgeType::Control));
}
