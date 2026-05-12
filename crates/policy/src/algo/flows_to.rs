//! Reachability helpers and tests for [`NodeQueries`](crate::NodeQueries).

use paralegal_pdg::{Node as SPDGNode, SPDGImpl, SPDG};

#[cfg(test)]
use paralegal_pdg::traverse::EdgeSelection;

use petgraph::visit::{Bfs, GraphBase, Visitable, Walker, WalkerIter};

#[cfg(test)]
use crate::NodeQueries;

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

impl Iterator for DataAndControlInfluencees<'_> {
    type Item = SPDGNode;
    fn next(&mut self) -> Option<Self::Item> {
        self.walker.next()
    }
}

#[test]
fn test_data_flows_to() {
    use paralegal_pdg::Identifier;
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx
        .controller_by_name(Identifier::new_intern("controller"))
        .unwrap();
    let src = ctx.controller_argument(controller, 0).unwrap();
    let sink1 = crate::test_utils::get_sink_node(&ctx, controller, "sink1");
    let sink2 = crate::test_utils::get_sink_node(&ctx, controller, "sink2");
    assert!(src.flows_to(&sink1, &ctx, EdgeSelection::Data));
    assert!(!src.flows_to(&sink2, &ctx, EdgeSelection::Data));
}

/// TODO: Make this test more stable. The use if `nth_successor` would be
/// replaced by something more robust.
#[test]
fn test_ctrl_flows_to() {
    use paralegal_pdg::Identifier;
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx
        .controller_by_name(Identifier::new_intern("controller_ctrl"))
        .unwrap();
    let src_a = ctx.controller_argument(controller, 0).unwrap();
    let src_b = ctx.controller_argument(controller, 1).unwrap();
    let src_c = ctx.controller_argument(controller, 2).unwrap();
    let cs1 = crate::test_utils::get_callsite_node(&ctx, controller, "sink1");
    let cs2 = crate::test_utils::get_callsite_node(&ctx, controller, "sink2");
    let switch_int_after_src_a = ctx.nth_successors(2, &src_a);
    let switch_int_after_src_c = ctx.nth_successors(2, &src_c);
    assert!(switch_int_after_src_a.flows_to(&cs1, &ctx, EdgeSelection::Control));
    assert!(switch_int_after_src_c.flows_to(&cs2, &ctx, EdgeSelection::Control));
    assert!(switch_int_after_src_a.flows_to(&cs2, &ctx, EdgeSelection::Control));
    assert!(!src_b.flows_to(&cs1, &ctx, EdgeSelection::Control));
    assert!(!src_b.flows_to(&cs2, &ctx, EdgeSelection::Control));
}

#[test]
fn test_flows_to() {
    use paralegal_pdg::Identifier;
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx
        .controller_by_name(Identifier::new_intern("controller_data_ctrl"))
        .unwrap();
    let src_a = ctx.controller_argument(controller, 0).unwrap();
    let src_b = ctx.controller_argument(controller, 1).unwrap();
    let sink = crate::test_utils::get_sink_node(&ctx, controller, "sink1");
    let cs = crate::test_utils::get_callsite_node(&ctx, controller, "sink1");
    // a flows to the sink1 callsite (by ctrl flow)
    assert!(src_a.flows_to(&cs, &ctx, EdgeSelection::Both));
    assert!(!src_a.flows_to(&cs, &ctx, EdgeSelection::Data));
    // b flows to the sink1 datasink (by data flow)
    assert!(src_b.flows_to(&sink, &ctx, EdgeSelection::Both));
    assert!(src_b.flows_to(&sink, &ctx, EdgeSelection::Data));
}

// Mirror of `test_flows_to` for an `async fn` controller. Argument nodes for
// async controllers are synthesized by `fix_async_args` rather than coming
// from the body's own root-Start places, so this test exercises a different
// `is_arg`-population path through `controller_argument`.
#[test]
fn test_async_controller_argument() {
    use paralegal_pdg::Identifier;
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx
        .controller_by_name(Identifier::new_intern("controller_async"))
        .unwrap();
    let src_a = ctx.controller_argument(controller, 0).unwrap();
    let src_b = ctx.controller_argument(controller, 1).unwrap();
    let sink = crate::test_utils::get_sink_node(&ctx, controller, "sink1");
    let cs = crate::test_utils::get_callsite_node(&ctx, controller, "sink1");
    assert!(src_a.flows_to(&cs, &ctx, EdgeSelection::Both));
    assert!(!src_a.flows_to(&cs, &ctx, EdgeSelection::Data));
    assert!(src_b.flows_to(&sink, &ctx, EdgeSelection::Both));
    assert!(src_b.flows_to(&sink, &ctx, EdgeSelection::Data));
}

// ---- shortest_path / flows_to parity ----
//
// `NodeExt::shortest_path` and `NodeQueries::flows_to` share the same BFS
// primitive ([`paralegal_pdg::traverse::bfs_reach`]) so they must agree on
// reachability — `shortest_path(...).is_some() == flows_to(...)` for any
// `(src, sink, edge_selection)`. These tests pin that invariant against the
// in-tree test crate and additionally check that any returned path is a valid
// forward edge chain in the chosen `EdgeSelection`.

#[cfg(test)]
fn path_is_valid_chain(
    ctx: &crate::RootContext,
    from: paralegal_pdg::GlobalNode,
    to: paralegal_pdg::GlobalNode,
    path: &[paralegal_pdg::GlobalNode],
    edge_selection: EdgeSelection,
) {
    if path.is_empty() {
        // The single-node case: source and target are the same SPDG node, so
        // the "path" is zero edges. `shortest_path` and `flows_to` agree this
        // is reachable; there are no edges to validate.
        assert_eq!(
            from, to,
            "empty path is only valid when source == target, got {from:?}→{to:?}"
        );
        return;
    }
    assert_eq!(
        *path.last().unwrap(),
        to,
        "path should end at the target: {from:?}→{to:?}, got {path:?}"
    );
    assert!(
        path.iter().all(|n| *n != from),
        "path must exclude the source: {from:?}→{to:?}, got {path:?}"
    );
    let spdg = &ctx.desc().controllers[&from.controller_id()];
    let mut prev = from.local_node();
    for step in path {
        let next = step.local_node();
        let has_edge = spdg
            .graph
            .edges_connecting(prev, next)
            .any(|e| edge_selection.conforms(e.weight().kind));
        assert!(
            has_edge,
            "no {edge_selection:?} edge from {prev:?} to {next:?} in path {from:?}→{to:?} (path so far: {path:?})"
        );
        prev = next;
    }
}

#[test]
fn shortest_path_returns_valid_chain_data() {
    use paralegal_pdg::{traverse::EdgeSelection, IntoIterGlobalNodes};
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx
        .controller_by_name(paralegal_pdg::Identifier::new_intern(
            "controller_data_ctrl",
        ))
        .unwrap();
    let src_b = ctx.controller_argument(controller, 1).unwrap();
    let sink = crate::test_utils::get_sink_node(&ctx, controller, "sink1");
    let from = src_b.iter_global_nodes().next().expect("src_b is empty");
    let to = sink.iter_global_nodes().next().expect("sink is empty");
    let path = crate::NodeExt::shortest_path(from, to, &ctx, EdgeSelection::Data)
        .expect("src_b should reach sink1 via Data");
    path_is_valid_chain(&ctx, from, to, &path, EdgeSelection::Data);
}

#[test]
fn shortest_path_returns_none_for_data_unreachable() {
    use paralegal_pdg::{traverse::EdgeSelection, IntoIterGlobalNodes};
    let ctx = crate::test_utils::test_ctx();
    let controller = ctx
        .controller_by_name(paralegal_pdg::Identifier::new_intern(
            "controller_data_ctrl",
        ))
        .unwrap();
    let src_a = ctx.controller_argument(controller, 0).unwrap();
    let cs = crate::test_utils::get_callsite_node(&ctx, controller, "sink1");
    // src_a reaches the sink1 callsite only by control flow, not data.
    let from = src_a.iter_global_nodes().next().expect("src_a is empty");
    for to in cs.iter_global_nodes() {
        assert!(
            crate::NodeExt::shortest_path(from, to, &ctx, EdgeSelection::Data).is_none(),
            "src_a should not reach the sink1 callsite via Data: from={from:?} to={to:?}"
        );
        assert!(
            crate::NodeExt::shortest_path(from, to, &ctx, EdgeSelection::Both).is_some(),
            "src_a should reach the sink1 callsite via Both: from={from:?} to={to:?}"
        );
    }
}

#[test]
fn shortest_path_flows_to_parity() {
    // Exhaustive per-pair parity check across the controllers in the test crate:
    // for every (src, sink) pair of nodes drawn from the marked clusters, and
    // every EdgeSelection, `shortest_path(..).is_some()` and `flows_to(..)` must
    // return the same answer. If they ever disagree, one of the two has drifted
    // off the shared `bfs_reach` primitive.
    use paralegal_pdg::{traverse::EdgeSelection, GlobalNode, Identifier, IntoIterGlobalNodes};
    let ctx = crate::test_utils::test_ctx();
    let selections = [
        EdgeSelection::Data,
        EdgeSelection::Control,
        EdgeSelection::Both,
    ];
    let cases: &[(&str, &[&str], &[&str])] = &[
        ("controller", &["sink1", "sink2"], &["sink1", "sink2"]),
        ("controller_data_ctrl", &["sink1"], &["sink1", "cond"]),
        ("controller_ctrl", &["sink1", "sink2"], &["sink1", "sink2"]),
        ("controller_async", &["sink1"], &["sink1"]),
    ];
    let mut pair_count = 0u32;
    for (ctrl_name, callsite_names, sink_names) in cases {
        let controller = ctx
            .controller_by_name(Identifier::new_intern(ctrl_name))
            .expect(ctrl_name);
        let mut sources: Vec<GlobalNode> = Vec::new();
        // Controller arguments — query indices 0..3, skip any missing.
        for idx in 0..3 {
            if let Some(arg) = ctx.controller_argument(controller, idx) {
                sources.extend(arg.iter_global_nodes());
            }
        }
        for name in *callsite_names {
            sources.extend(
                crate::test_utils::get_callsite_node(&ctx, controller, name).iter_global_nodes(),
            );
        }
        let mut sinks: Vec<GlobalNode> = Vec::new();
        for name in *sink_names {
            sinks.extend(
                crate::test_utils::get_sink_node(&ctx, controller, name).iter_global_nodes(),
            );
            sinks.extend(
                crate::test_utils::get_callsite_node(&ctx, controller, name).iter_global_nodes(),
            );
        }
        for &src in &sources {
            for &snk in &sinks {
                for &sel in &selections {
                    let sp = crate::NodeExt::shortest_path(src, snk, &ctx, sel);
                    let ft = crate::NodeQueries::flows_to(src, snk, &ctx, sel);
                    assert_eq!(
                        sp.is_some(),
                        ft,
                        "parity break in {ctrl_name}: src={src:?} snk={snk:?} sel={sel:?} sp.is_some()={} ft={}",
                        sp.is_some(),
                        ft,
                    );
                    if let Some(path) = sp {
                        path_is_valid_chain(&ctx, src, snk, &path, sel);
                    }
                    pair_count += 1;
                }
            }
        }
    }
    assert!(
        pair_count > 0,
        "parity test exercised no pairs — fixture selection likely broken"
    );
}
