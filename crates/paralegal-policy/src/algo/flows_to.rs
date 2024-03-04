//! Precomputed reachability queries

use paralegal_spdg::{Node as SPDGNode, SPDGImpl, SPDG};

use bitvec::vec::BitVec;

use std::fmt;

#[cfg(test)]
use paralegal_spdg::traverse::EdgeSelection;

/// Precomputed indices for common queries of a PDG.
pub struct CtrlFlowsTo {
    /// The densely packed transitive closure of the
    /// [`paralegal_spdg::EdgeKind::Data`] edges.
    pub data_flows_to: Vec<BitVec>,
}

impl CtrlFlowsTo {
    /// Constructs the transitive closure from a [`SPDG`].
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
                            changed |= !flows_to[src_idx][sink_idx];
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

/// An [`Iterator`] over the [`SPDGNode`]s from the given src in
/// the transitive closure of data and control flow of the given [`SPDG`].
pub struct DataAndControlInfluencees<'a> {
    walker: WalkerIter<
        Bfs<<SPDGImpl as GraphBase>::NodeId, <SPDGImpl as Visitable>::Map>,
        &'a SPDGImpl,
    >,
}

impl<'a> DataAndControlInfluencees<'a> {
    /// Create a new iterator that iterates through nodes
    /// that depend on the provided src in the provided
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
    let sink1 = crate::test_utils::get_sink_node(&ctx, controller, "sink1");
    let sink2 = crate::test_utils::get_sink_node(&ctx, controller, "sink2");
    assert!(ctx.flows_to(src, &sink1, EdgeSelection::Data));
    assert!(!ctx.flows_to(src, &sink2, EdgeSelection::Data));
}

/// TODO: Make this test more stable. The use if `nth_successor` whould be
/// replaced by something more robust.
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
    let cs1 = crate::test_utils::get_callsite_node(&ctx, controller, "sink1");
    let cs2 = crate::test_utils::get_callsite_node(&ctx, controller, "sink2");
    let switch_int_after_src_a = ctx.nth_successors(2, src_a);
    let switch_int_after_src_c = ctx.nth_successors(2, src_c);
    assert!(ctx.flows_to(&switch_int_after_src_a, &cs1, EdgeSelection::Control));
    assert!(ctx.flows_to(&switch_int_after_src_c, &cs2, EdgeSelection::Control));
    assert!(ctx.flows_to(
        dbg!(&switch_int_after_src_a),
        dbg!(&cs2),
        EdgeSelection::Control
    ));
    assert!(!ctx.flows_to(src_b, &cs1, EdgeSelection::Control));
    assert!(!ctx.flows_to(src_b, &cs2, EdgeSelection::Control));
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
    let sink = crate::test_utils::get_sink_node(&ctx, controller, "sink1");
    let cs = crate::test_utils::get_callsite_node(&ctx, controller, "sink1");
    // a flows to the sink1 callsite (by ctrl flow)
    assert!(ctx.flows_to(src_a, &cs, EdgeSelection::Both));
    assert!(!ctx.flows_to(src_a, &cs, EdgeSelection::Data));
    // b flows to the sink1 datasink (by data flow)
    assert!(ctx.flows_to(src_b, &sink, EdgeSelection::Both));
    assert!(ctx.flows_to(src_b, &sink, EdgeSelection::Data));
}
