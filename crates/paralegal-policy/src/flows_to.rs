use paralegal_spdg::{Node as SPDGNode, SPDGImpl, SPDG};

use bitvec::vec::BitVec;

use std::fmt;

/// The transitive closure of the [`Ctrl::data_flow`] relation.
///
/// Implemented efficiently using an [`IndexedDomain`] over the
/// [`DataSource`] and [`CallSiteOrDataSink`] types.
///
/// ## Relationship of [`CtrlFlowsTo::data_flows_to`], [`DataAndControlInfluencees`], [`crate::Context::flows_to()`], [`crate::Context::influencers()`] and [`crate::Context::influencees()`]
///
/// - [`CtrlFlowsTo::data_flows_to`] Index vs [`DataAndControlInfluencees`]:
/// The index is computed for efficiency only for [`crate::EdgeType::Data`] using the [`Ctrl::data_flow`].
/// [`DataAndControlInfluencees`] additionally uses [`Ctrl::ctrl_flow`] and is used for the
/// [`crate::EdgeType::DataAndControl`]. It uses a BFS rather than an index.
///
/// - [`CtrlFlowsTo`] and [`DataAndControlInfluencees`] vs functions in [`crate::Context`]:
/// [`CtrlFlowsTo`] and [`DataAndControlInfluencees`]
/// utilize [`DataSource`] to [`CallSiteOrDataSink`], so do not provide all of the
/// information that is needed answer questions about any kind of [`crate::Node`] and any
/// kind of [`crate::EdgeType`] in an intuitive way. The functions in [`crate::Context`] utilize
/// [`CtrlFlowsTo`] and [`DataAndControlInfluencees`].
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
/// [`crate::Context::influencees()`], querying [`CtrlFlowsTo::data_flows_to`] Index
/// vs [`DataAndControlInfluencees`] does not exhaustively
/// return all type of [`crate::Node`]s since they only provide either [`DataSource`]
/// influencers or [`CallSiteOrDataSink`] influencees.
/// So, these functions add the [`NodeType::CallArgument`]s related to each
/// [`NodeType::CallSite`] and the [`NodeType::CallSite`] related to each
/// [`NodeType::CallArgument`] respectively.
pub struct CtrlFlowsTo {
    // /// Mapping from [`CallSiteOrDataSink::CallSite`]s to the [`CallSiteOrDataSink::DataSink(CallArgument)`]s that they are related to.
    // pub callsites_to_callargs: std::collections::HashMap<SPDGNode, Vec<SPDGNode>>,
    /// The transitive closure of the [`Ctrl::data_flow`] relation.
    /// If a source flows to a [`DataSink::Argument`], it also flows into its CallSite.
    ///
    /// See the [`IndexMatrix`] documentation for details on how to
    /// query this representation of the relation.
    pub data_flows_to: Vec<BitVec>,
}

impl CtrlFlowsTo {
    /// Constructs the transitive closure from a [`Ctrl`].
    pub fn build(spdg: &SPDG) -> Self {
        use petgraph::prelude::*;
        let domain_size = spdg.graph.node_count();
        // Connect each function-argument sink to its corresponding function sources.
        // This lets us compute the transitive closure by following through the `sink_to_source` map.

        fn iterate(flows_to: &mut [BitVec]) {
            let mut changed = true;
            // Safety: We never resize/reallocate any of the vectors, so
            // mutating and reading them simultaneously is fine.
            let unsafe_flow_ref: &'_ [BitVec] =
                unsafe { std::mem::transmute::<&&mut [BitVec], &&[BitVec]>(&flows_to) };
            while changed {
                changed = false;
                for src_idx in 0..flows_to.len() {
                    for intermediate_idx in unsafe_flow_ref[src_idx].iter_ones() {
                        for sink_idx in unsafe_flow_ref[intermediate_idx].iter_ones() {
                            changed |= flows_to[src_idx][sink_idx];
                            flows_to[src_idx].set(sink_idx, true);
                        }
                    }
                }
            }
        }

        let mut data_flows_to = vec![BitVec::repeat(false, domain_size); domain_size];

        // Initialize the `flows_to` relation with the data provided by `Ctrl::data_flow`.
        for edge in spdg
            .graph
            .edge_references()
            .filter(|e| e.weight().is_data())
        {
            data_flows_to[edge.source().index()].set(edge.target().index(), true);
        }

        iterate(&mut data_flows_to);

        CtrlFlowsTo {
            //callsites_to_callargs,
            data_flows_to,
        }
    }
}

use petgraph::visit::{Bfs, GraphBase, Visitable, Walker, WalkerIter};

/// An [`Iterator`] over the [`CallSiteOrDataSink`]s from the given src in
/// the transitive closure of data and control flow of the given [`Ctrl`].
pub struct DataAndControlInfluencees<'a> {
    walker: WalkerIter<
        Bfs<<SPDGImpl as GraphBase>::NodeId, <SPDGImpl as Visitable>::Map>,
        &'a SPDGImpl,
    >,
}

impl<'a> DataAndControlInfluencees<'a> {
    /// Create a new DataAndControlInfluencees iterator that iterates through
    /// [`CallSiteOrDataSink`]s that depend on the provided src in the provided
    /// controller.
    pub fn new(src: SPDGNode, ctrl: &'a SPDG) -> Self {
        let bfs = Bfs::new(&ctrl.graph, src);
        let walker_iter = Walker::iter(bfs, &ctrl.graph);
        Self {
            walker: walker_iter,
        }
    }
}

impl<'a> Iterator for DataAndControlInfluencees<'a> {
    type Item = SPDGNode;
    fn next(&mut self) -> Option<Self::Item> {
        self.walker.next()
    }
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
    use paralegal_spdg::Identifier;
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx
        .controller_by_name(Identifier::new_intern("controller"))
        .unwrap();
    let src = ctx.controller_argument(controller, 0).unwrap();
    let sink1 = crate::test_utils::get_sink_node(&ctx, controller, "sink1").unwrap();
    let sink2 = crate::test_utils::get_sink_node(&ctx, controller, "sink2").unwrap();
    assert!(ctx.flows_to(src, sink1, crate::EdgeType::Data));
    assert!(!ctx.flows_to(src, sink2, crate::EdgeType::Data));
}

#[test]
fn test_ctrl_flows_to() {
    use paralegal_spdg::Identifier;
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx
        .controller_by_name(Identifier::new_intern("controller_ctrl"))
        .unwrap();
    let src_a = ctx.controller_argument(controller, 0).unwrap();
    let src_b = ctx.controller_argument(controller, 1).unwrap();
    let src_c = ctx.controller_argument(controller, 2).unwrap();
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
    use paralegal_spdg::Identifier;
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx
        .controller_by_name(Identifier::new_intern("controller_data_ctrl"))
        .unwrap();
    let src_a = ctx.controller_argument(controller, 0).unwrap();
    let src_b = ctx.controller_argument(controller, 1).unwrap();
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
    use paralegal_spdg::Identifier;
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx
        .controller_by_name(Identifier::new_intern("controller_data_ctrl"))
        .unwrap();
    let sink = crate::test_utils::get_sink_node(&ctx, controller, "sink1").unwrap();
    let cs = crate::test_utils::get_callsite_node(&ctx, controller, "sink1").unwrap();

    assert!(ctx.flows_to(sink, cs, crate::EdgeType::Data));
    assert!(ctx.flows_to(sink, cs, crate::EdgeType::DataAndControl));
    assert!(!ctx.flows_to(sink, cs, crate::EdgeType::Control));
}
