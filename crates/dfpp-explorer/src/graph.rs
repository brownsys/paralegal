//! Defines the basic graph data structure the explorer works on and adapters
//! which can change the behavior of a graph witout copies.

use dfpp::{
    ana::inline::{Edge, EdgeType},
    ir::GlobalLocation,
};

use petgraph::visit::{
    Data, EdgeRef, GraphBase, GraphRef, IntoEdgeReferences, IntoEdges, IntoEdgesDirected,
    IntoNeighbors, IntoNeighborsDirected, IntoNodeIdentifiers, NodeCount, NodeIndexable, Visitable,
};

/// The canonical representation fo a graph used by the explorer.
pub type Graph<'g> = petgraph::graphmap::GraphMap<Node<'g>, Edge, petgraph::Directed>;

/// Assigns an edge weight via a closure.
pub struct WithWeightedEdges<'f, G: IntoEdgeReferences> {
    graph: G,
    weight: &'f dyn Fn(G::EdgeRef) -> f32,
}

impl<'f, G: IntoEdgeReferences> WithWeightedEdges<'f, G> {
    pub fn new(graph: G, weight: &'f dyn Fn(G::EdgeRef) -> f32) -> Self {
        Self { graph, weight }
    }
}

impl<'f, G: Data + IntoEdgeReferences> Data for WithWeightedEdges<'f, G> {
    type NodeWeight = G::NodeWeight;
    type EdgeWeight = f32;
}

#[derive(Clone, Copy)]
pub struct WeightedEdgeRef<E> {
    original_ref: E,
    weight: f32,
}

impl<E: EdgeRef> EdgeRef for WeightedEdgeRef<E> {
    type EdgeId = E::EdgeId;
    type NodeId = E::NodeId;
    type Weight = f32;
    fn source(&self) -> Self::NodeId {
        self.original_ref.source()
    }
    fn target(&self) -> Self::NodeId {
        self.original_ref.target()
    }
    fn id(&self) -> Self::EdgeId {
        self.original_ref.id()
    }
    fn weight(&self) -> &Self::Weight {
        &self.weight
    }
}

/// One of the iterators for [`WithWeightedEdges`] that are needed to run the
/// algorithms in [`petgraph`].
pub struct WeightedEdgeReferences<'f, E, I> {
    inner: I,
    get_weight: &'f dyn Fn(E) -> f32,
}

impl<'f, E: EdgeRef, I: Iterator<Item = E>> Iterator for WeightedEdgeReferences<'f, E, I> {
    type Item = WeightedEdgeRef<E>;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|ef| WeightedEdgeRef {
            original_ref: ef,
            weight: (self.get_weight)(ef),
        })
    }
}

impl<'f, G: IntoEdgeReferences> IntoEdgeReferences for &'_ WithWeightedEdges<'f, G>
where
    G::EdgeReferences: 'f,
    G::NodeId: 'f,
{
    type EdgeRef = WeightedEdgeRef<G::EdgeRef>;
    type EdgeReferences = WeightedEdgeReferences<'f, G::EdgeRef, G::EdgeReferences>;

    fn edge_references(self) -> Self::EdgeReferences {
        WeightedEdgeReferences {
            inner: self.graph.edge_references(),
            get_weight: self.weight,
        }
    }
}

impl<'f, G: IntoEdges> IntoEdges for &'_ WithWeightedEdges<'f, G>
where
    G::EdgeReferences: 'f,
    G::NodeId: 'f,
{
    type Edges = WeightedEdgeReferences<'f, G::EdgeRef, G::Edges>;

    fn edges(self, a: Self::NodeId) -> Self::Edges {
        WeightedEdgeReferences {
            inner: self.graph.edges(a),
            get_weight: self.weight,
        }
    }
}

impl<'f, G: IntoNeighbors + IntoEdgeReferences> IntoNeighbors for &'_ WithWeightedEdges<'f, G> {
    type Neighbors = <G as IntoNeighbors>::Neighbors;

    fn neighbors(self, a: Self::NodeId) -> Self::Neighbors {
        self.graph.neighbors(a)
    }
}

impl<'f, G: GraphBase + IntoEdgeReferences> GraphBase for WithWeightedEdges<'f, G> {
    type EdgeId = <G as GraphBase>::EdgeId;
    type NodeId = <G as GraphBase>::NodeId;
}

impl<'f, G: NodeIndexable + IntoEdgeReferences> NodeIndexable for &'_ WithWeightedEdges<'f, G> {
    fn from_index(&self, i: usize) -> Self::NodeId {
        self.graph.from_index(i)
    }
    fn node_bound(&self) -> usize {
        self.graph.node_bound()
    }
    fn to_index(&self, a: Self::NodeId) -> usize {
        self.graph.to_index(a)
    }
}

impl<'f, G: NodeCount + IntoEdgeReferences> NodeCount for &'_ WithWeightedEdges<'f, G> {
    fn node_count(&self) -> usize {
        self.graph.node_count()
    }
}

impl<'f, G: IntoNodeIdentifiers + IntoEdgeReferences> IntoNodeIdentifiers
    for &'_ WithWeightedEdges<'f, G>
{
    type NodeIdentifiers = <G as IntoNodeIdentifiers>::NodeIdentifiers;
    fn node_identifiers(self) -> Self::NodeIdentifiers {
        self.graph.node_identifiers()
    }
}

/// Hide control edges in the usual iterators.
#[derive(Clone, Copy)]
pub struct IgnoreCtrlEdges<G>(G);

impl<G> From<G> for IgnoreCtrlEdges<G> {
    fn from(value: G) -> Self {
        Self(value)
    }
}

impl<G: NodeCount> NodeCount for IgnoreCtrlEdges<G> {
    fn node_count(&self) -> usize {
        self.0.node_count()
    }
}

impl<G: Visitable> Visitable for IgnoreCtrlEdges<G> {
    type Map = G::Map;

    fn visit_map(&self) -> Self::Map {
        self.0.visit_map()
    }

    fn reset_map(&self, map: &mut Self::Map) {
        self.0.reset_map(map)
    }
}

/// Node representation as used by the canonical [`Graph`].
#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct Node<'g>(Option<GlobalLocation<'g>>);

impl<'g> Node<'g> {
    pub fn return_() -> Self {
        Self(None)
    }

    /// `None` means this is the return node
    pub fn location(self) -> Option<GlobalLocation<'g>> {
        self.0
    }
}

impl<'g> From<GlobalLocation<'g>> for Node<'g> {
    fn from(loc: GlobalLocation<'g>) -> Self {
        Self(Some(loc))
    }
}

impl<'g> std::fmt::Display for Node<'g> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(n) = self.0 {
            n.fmt(f)
        } else {
            f.write_str("return")
        }
    }
}

/// One of the iterators for [`IgnoreCtrlEdges`] that are needed to run the
/// algorithms in [`petgraph`].
pub struct NoCtrlNeighbors<E, I: Iterator<Item = E>> {
    inner: I,
    direction: petgraph::Direction,
}

impl<E: EdgeRef<Weight = Edge>, I: Iterator<Item = E>> std::iter::Iterator
    for NoCtrlNeighbors<E, I>
{
    type Item = E::NodeId;
    fn next(&mut self) -> Option<Self::Item> {
        let eref = self.inner.next()?;
        let mut weight = *eref.weight();
        weight.remove_type(EdgeType::Control);
        (!weight.is_empty())
            .then_some(if self.direction == petgraph::Direction::Outgoing {
                eref.target()
            } else {
                eref.source()
            })
            .or_else(|| self.next())
    }
}

/// One of the iterators for [`IgnoreCtrlEdges`] that are needed to run the
/// algorithms in [`petgraph`].
///
/// This is confusingly named I know, but the actual graph is
/// [`IgnoreCtrlEdges`], wheras this is an iterator over edges with control
/// edges ignored.
pub struct NoCtrlEdges<E, I: Iterator<Item = E>>(I);

impl<E: EdgeRef<Weight = Edge>, I: Iterator<Item = E>> std::iter::Iterator for NoCtrlEdges<E, I> {
    type Item = E;
    fn next(&mut self) -> Option<Self::Item> {
        let eref = self.0.next()?;
        let mut weight = *eref.weight();
        weight.remove_type(EdgeType::Control);
        (!weight.is_empty()).then_some(eref).or_else(|| self.next())
    }
}

impl<G: IntoEdgesDirected + Data<EdgeWeight = Edge>> IntoNeighborsDirected for IgnoreCtrlEdges<G> {
    type NeighborsDirected = NoCtrlNeighbors<G::EdgeRef, G::EdgesDirected>;
    fn neighbors_directed(
        self,
        n: Self::NodeId,
        d: petgraph::Direction,
    ) -> Self::NeighborsDirected {
        NoCtrlNeighbors {
            inner: self.0.edges_directed(n, d),
            direction: d,
        }
    }
}

impl<G: GraphBase> petgraph::visit::GraphBase for IgnoreCtrlEdges<G> {
    type EdgeId = G::EdgeId;
    type NodeId = G::NodeId;
}

impl<G: GraphRef> GraphRef for IgnoreCtrlEdges<G> {}

impl<G: IntoEdges + Data<EdgeWeight = Edge>> petgraph::visit::IntoNeighbors for IgnoreCtrlEdges<G> {
    type Neighbors = NoCtrlNeighbors<G::EdgeRef, G::Edges>;
    fn neighbors(self, a: Self::NodeId) -> Self::Neighbors {
        NoCtrlNeighbors {
            inner: self.0.edges(a),
            direction: petgraph::Outgoing,
        }
    }
}

impl<G: Data> Data for IgnoreCtrlEdges<G> {
    type EdgeWeight = G::EdgeWeight;
    type NodeWeight = G::NodeWeight;
}

impl<G: IntoEdgeReferences + Data<EdgeWeight = Edge>> IntoEdgeReferences for IgnoreCtrlEdges<G> {
    type EdgeRef = G::EdgeRef;
    type EdgeReferences = NoCtrlEdges<Self::EdgeRef, G::EdgeReferences>;

    fn edge_references(self) -> Self::EdgeReferences {
        NoCtrlEdges(self.0.edge_references())
    }
}

impl<G: IntoNodeIdentifiers> IntoNodeIdentifiers for IgnoreCtrlEdges<G> {
    type NodeIdentifiers = G::NodeIdentifiers;

    fn node_identifiers(self) -> Self::NodeIdentifiers {
        self.0.node_identifiers()
    }
}

impl<G: IntoEdges + Data<EdgeWeight = Edge>> IntoEdges for IgnoreCtrlEdges<G> {
    type Edges = NoCtrlEdges<G::EdgeRef, G::Edges>;
    fn edges(self, a: Self::NodeId) -> Self::Edges {
        NoCtrlEdges(self.0.edges(a))
    }
}

impl<G: IntoEdgesDirected + Data<EdgeWeight = Edge>> IntoEdgesDirected for IgnoreCtrlEdges<G> {
    type EdgesDirected = NoCtrlEdges<G::EdgeRef, G::EdgesDirected>;

    fn edges_directed(self, a: Self::NodeId, dir: petgraph::Direction) -> Self::EdgesDirected {
        NoCtrlEdges(self.0.edges_directed(a, dir))
    }
}

impl<G: NodeIndexable> NodeIndexable for IgnoreCtrlEdges<G> {
    fn from_index(&self, i: usize) -> Self::NodeId {
        self.0.from_index(i)
    }
    fn node_bound(&self) -> usize {
        self.0.node_bound()
    }
    fn to_index(&self, a: Self::NodeId) -> usize {
        self.0.to_index(a)
    }
}
