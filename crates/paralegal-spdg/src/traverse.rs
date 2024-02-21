//! Utilities for traversing an SPDG

use std::collections::HashSet;

use petgraph::visit::{Control, Data, DfsEvent, EdgeFiltered, EdgeRef, IntoEdgeReferences};

use crate::{EdgeInfo, EdgeKind, Node};

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
) -> bool {
    let targets = other.into_iter().collect::<HashSet<_>>();
    let mut from = from.into_iter().peekable();
    if from.peek().is_none() || targets.is_empty() {
        return false;
    }

    let graph = edge_selection.filter_graph(&spdg.graph);

    let result = petgraph::visit::depth_first_search(&graph, from, |event| match event {
        DfsEvent::Discover(d, _) if targets.contains(&d) => Control::Break(()),
        _ => Control::Continue,
    });
    matches!(result, Control::Break(()))
}
