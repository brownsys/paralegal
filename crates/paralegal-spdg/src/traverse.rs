//! Utilities for traversing an SPDG

use std::collections::HashSet;

use petgraph::visit::{
    Bfs, Control, Data, DfsEvent, EdgeFiltered, EdgeRef, IntoEdgeReferences, IntoEdges,
    IntoEdgesDirected, IntoNeighbors, VisitMap, Visitable, Walker, WalkerIter,
};

use crate::{EdgeInfo, EdgeKind, Node, SPDGImpl};

use super::SPDG;

/// Which type of edges should be considered for a given traversal
#[derive(Clone, Copy, Eq, PartialEq, strum::EnumIs)]
pub enum EdgeSelection {
    /// Consider only edges with [`crate::EdgeKind::Data`]
    Data,
    /// Consider only edges with [`crate::EdgeKind::Control`]
    Control,
    /// Consider both data and control flow edges in any combination
    Both,
}

impl EdgeSelection {
    /// Does this selection admit edges of type [`crate::EdgeKind::Control`]
    pub fn use_control(self) -> bool {
        matches!(self, EdgeSelection::Control | EdgeSelection::Both)
    }
    /// Does this selection admit edges of type [`crate::EdgeKind::Data`]
    pub fn use_data(self) -> bool {
        matches!(self, EdgeSelection::Data | EdgeSelection::Both)
    }

    /// Is this edge kind admissible?
    pub fn conforms(self, kind: EdgeKind) -> bool {
        matches!(
            (self, kind),
            (EdgeSelection::Both, _)
                | (EdgeSelection::Data, EdgeKind::Data)
                | (EdgeSelection::Control, EdgeKind::Control)
        )
    }

    /// Create a graph adaptor that implements this edge selection.
    pub fn filter_graph<G: IntoEdgeReferences + Data<EdgeWeight = EdgeInfo>>(
        self,
        g: G,
    ) -> EdgeFiltered<G, fn(G::EdgeRef) -> bool> {
        fn data_only<E: EdgeRef<Weight = EdgeInfo>>(e: E) -> bool {
            e.weight().is_data()
        }
        fn control_only<E: EdgeRef<Weight = EdgeInfo>>(e: E) -> bool {
            e.weight().is_control()
        }
        fn all_edges<E: EdgeRef<Weight = EdgeInfo>>(_: E) -> bool {
            true
        }

        match self {
            EdgeSelection::Data => EdgeFiltered(g, data_only as fn(G::EdgeRef) -> bool),
            EdgeSelection::Control => EdgeFiltered(g, control_only as fn(G::EdgeRef) -> bool),
            EdgeSelection::Both => EdgeFiltered(g, all_edges as fn(G::EdgeRef) -> bool),
        }
    }
}

/// A primitive that queries whether we can reach from one set of nodes to
/// another
pub fn generic_flows_to(
    from: impl IntoIterator<Item = Node>,
    edge_selection: EdgeSelection,
    spdg: &SPDG,
    other: impl IntoIterator<Item = Node>,
) -> Option<Node> {
    let targets = other.into_iter().collect::<HashSet<_>>();
    let mut from = from.into_iter().peekable();
    if from.peek().is_none() || targets.is_empty() {
        return None;
    }

    let graph = edge_selection.filter_graph(&spdg.graph);

    let result = petgraph::visit::depth_first_search(&graph, from, |event| match event {
        DfsEvent::Discover(d, _) if targets.contains(&d) => Control::Break(d),
        _ => Control::Continue,
    });
    match result {
        Control::Break(r) => Some(r),
        _ => None,
    }
}

/// The current policy for this iterator is that it does not return the start
/// nodes *uness* there is a cycle and a node is reachable that way.
fn bfs_iter<G: IntoNeighbors + Visitable<NodeId = Node, Map = <SPDGImpl as Visitable>::Map>>(
    g: G,
    start: impl IntoIterator<Item = Node>,
) -> WalkerIter<Bfs<Node, <G as Visitable>::Map>, G> {
    let mut discovered = g.visit_map();
    let mut stack: std::collections::VecDeque<petgraph::prelude::NodeIndex> = Default::default();
    // prime the stack with all input nodes, otherwise they would be returned
    // from the iterator.
    for n in start {
        for next in g.neighbors(n) {
            if discovered.visit(next) {
                stack.push_back(next);
            }
        }
    }
    let bfs = Bfs { stack, discovered };
    Walker::iter(bfs, g)
}

#[cfg(test)]
mod test {
    use petgraph::graph::DiGraph;

    use super::bfs_iter;

    #[test]
    fn iter_sees_nested() {
        let mut g = DiGraph::<(), ()>::new();
        let a = g.add_node(());
        let b = g.add_node(());
        let c = g.add_node(());
        let d = g.add_node(());

        g.add_edge(a, b, ());
        g.add_edge(b, c, ());

        let seen = bfs_iter(&g, [a]).collect::<Vec<_>>();
        assert!(seen.contains(&b));
        assert!(seen.contains(&c));
        assert!(!seen.contains(&d));
        assert!(!seen.contains(&a));
    }

    #[test]
    fn iter_sees_cycle() {
        let mut g = DiGraph::<(), ()>::new();
        let a = g.add_node(());
        let b = g.add_node(());
        let c = g.add_node(());

        g.add_edge(a, b, ());
        g.add_edge(b, c, ());
        g.add_edge(c, a, ());

        let seen = bfs_iter(&g, [a]).collect::<Vec<_>>();
        assert!(seen.contains(&b));
        assert!(seen.contains(&c));
        assert!(seen.contains(&a));
    }
}

/// Base function for implementing influencers
pub fn generic_influencers<
    G: IntoEdgesDirected
        + Visitable<NodeId = Node, Map = <SPDGImpl as Visitable>::Map>
        + Data<EdgeWeight = EdgeInfo>,
>(
    g: G,
    nodes: impl IntoIterator<Item = Node>,
    edge_selection: EdgeSelection,
) -> Vec<Node> {
    use petgraph::visit::*;

    let reversed_graph = Reversed(g);

    match edge_selection {
        EdgeSelection::Data => {
            let edges_filtered = EdgeFiltered::from_fn(reversed_graph, |e| e.weight().is_data());
            bfs_iter(&edges_filtered, nodes).collect::<Vec<_>>()
        }
        EdgeSelection::Control => {
            let edges_filtered = EdgeFiltered::from_fn(reversed_graph, |e| e.weight().is_control());
            bfs_iter(&edges_filtered, nodes).collect::<Vec<_>>()
        }
        EdgeSelection::Both => bfs_iter(reversed_graph, nodes).collect::<Vec<_>>(),
    }
}

/// Base function for implementing influencees
pub fn generic_influencees<
    G: IntoEdges
        + Visitable<NodeId = Node, Map = <SPDGImpl as Visitable>::Map>
        + Data<EdgeWeight = EdgeInfo>,
>(
    g: G,
    nodes: impl IntoIterator<Item = Node>,
    edge_selection: EdgeSelection,
) -> Vec<Node> {
    use petgraph::visit::*;

    match edge_selection {
        EdgeSelection::Data => {
            let edges_filtered = EdgeFiltered::from_fn(g, |e| e.weight().is_data());
            bfs_iter(&edges_filtered, nodes).collect::<Vec<_>>()
        }
        EdgeSelection::Control => {
            let edges_filtered = EdgeFiltered::from_fn(g, |e| e.weight().is_control());
            bfs_iter(&edges_filtered, nodes).collect::<Vec<_>>()
        }
        EdgeSelection::Both => bfs_iter(g, nodes).collect::<Vec<_>>(),
    }
}
