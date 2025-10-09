use petgraph::visit::IntoNodeReferences;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{HasLocalDecls, Local, LocalDecl, LocalDecls, Location, Place},
    ty::{GenericArgsRef, Instance},
};

use super::graph_elems::{DepEdge, DepNode, DepNodeKind, OneHopLocation};
use crate::constants::PlaceOrConst;

pub type Node = petgraph::graph::NodeIndex;

#[derive(Debug, Clone)]
pub struct PartialGraph<'tcx, K> {
    node_mapping: FxHashMap<(PlaceOrConst<'tcx>, OneHopLocation), Node>,
    graph: petgraph::Graph<DepNode<'tcx, OneHopLocation>, DepEdge<OneHopLocation>>,
    pub(crate) def_id: DefId,
    arg_count: usize,
    pub(crate) generics: GenericArgsRef<'tcx>,
    local_decls: IndexVec<Local, LocalDecl<'tcx>>,
    #[allow(dead_code)]
    pub(crate) k: K,
    pub(crate) inlined_calls: Vec<(
        Location,
        Instance<'tcx>,
        K,
        Vec<GraphConnectionPoint<'tcx, OneHopLocation>>,
    )>,
}

pub type GraphConnectionPoint<'tcx, Loc> = (Node, DepEdge<Loc>);

impl<'tcx, K> HasLocalDecls<'tcx> for PartialGraph<'tcx, K> {
    fn local_decls(&self) -> &LocalDecls<'tcx> {
        &self.local_decls
    }
}

impl<'tcx, K> PartialGraph<'tcx, K> {
    pub(crate) fn new(
        generics: GenericArgsRef<'tcx>,
        def_id: DefId,
        arg_count: usize,
        local_decls: &LocalDecls<'tcx>,
        k: K,
    ) -> Self {
        Self {
            node_mapping: Default::default(),
            graph: petgraph::Graph::new(),
            generics,
            def_id,
            arg_count,
            local_decls: local_decls.to_owned(),
            inlined_calls: Default::default(),
            k,
        }
    }

    pub fn def_id(&self) -> DefId {
        self.def_id
    }

    pub(crate) fn insert_node(&mut self, node: DepNode<'tcx, OneHopLocation>) -> Node {
        self.get_or_construct_node(node.make_descriptor(), node.at.clone(), || node)
    }

    pub fn get_place_node(&self, place: Place<'tcx>, at: OneHopLocation) -> Option<Node> {
        self.get_node(place.into(), at)
    }

    pub fn get_node(&self, place: PlaceOrConst<'tcx>, at: OneHopLocation) -> Option<Node> {
        self.node_mapping.get(&(place, at)).copied()
    }

    pub(crate) fn get_or_construct_node(
        &mut self,
        place: PlaceOrConst<'tcx>,
        at: OneHopLocation,
        construct: impl FnOnce() -> DepNode<'tcx, OneHopLocation>,
    ) -> Node {
        if let Some(node) = self.get_node(place, at.clone()) {
            node
        } else {
            let node = construct();
            let idx = self.graph.add_node(node);
            self.node_mapping.insert((place, at), idx);
            idx
        }
    }

    pub(crate) fn insert_edge(
        &mut self,
        source: Node,
        target: Node,
        edge: DepEdge<OneHopLocation>,
    ) {
        if let Some(prior) = self.graph.find_edge(source, target) {
            let e = self.graph.edge_weight(prior).unwrap();
            assert_eq!(
                e,
                &edge,
                "Edge {} -> {} already exists in {:?}",
                self.node_props(source), //.display_place(),
                self.node_props(target), //.display_place(),
                self.def_id
            );
        } else {
            self.graph.add_edge(source, target, edge);
        }
    }

    pub fn iter_nodes(
        &self,
    ) -> impl Iterator<Item = (Node, &DepNode<'tcx, OneHopLocation>)> + Clone {
        self.graph.node_references()
    }

    pub fn iter_edges<'a>(
        &'a self,
    ) -> impl Iterator<Item = (Node, Node, &'a DepEdge<OneHopLocation>)> + use<'tcx, 'a, K> {
        use petgraph::visit::EdgeRef;
        self.graph
            .edge_references()
            .map(|r| (r.source(), r.target(), r.weight()))
    }

    pub fn node_props(&self, node: Node) -> &DepNode<'tcx, OneHopLocation> {
        self.graph.node_weight(node).unwrap()
    }

    /// Returns the set of source places that the parent can access (write to)
    pub(crate) fn parentable_srcs<'a>(&'a self) -> FxHashSet<(DepNode<'tcx, bool>, Option<u8>)> {
        self.iter_edges()
            .filter(|&(n, _, _)| self.node_props(n).at.location.is_start())
            .map(|(n, _, _)| {
                let n = self.node_props(n);
                n.map_at(|_| {
                    assert!(n.at.in_child.is_none());
                    true
                })
            })
            .filter_map(move |a| {
                let as_arg = as_arg(&a, self.arg_count)?;
                Some((a, as_arg))
            })
            .collect()
    }

    /// Returns the set of destination places that the parent can access (read
    /// from)
    pub(crate) fn parentable_dsts<'a>(&'a self) -> FxHashSet<(DepNode<'tcx, bool>, Option<u8>)> {
        self.iter_nodes()
            .map(|(_, n)| n)
            .filter(|n| n.at.location.is_end())
            .map(|n| {
                assert!(n.at.in_child.is_none());
                n.map_at(|_| false)
            })
            .filter_map(move |a| {
                let arg = as_arg(&a, self.arg_count)?;
                Some((a, arg))
            })
            .collect()
    }

    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }

    pub fn raw(&self) -> &petgraph::Graph<DepNode<'tcx, OneHopLocation>, DepEdge<OneHopLocation>> {
        &self.graph
    }
}

fn as_arg<Loc>(node: &DepNode<'_, Loc>, arg_count: usize) -> Option<Option<u8>> {
    let DepNodeKind::Place(node) = &node.kind else {
        return None;
    };
    let local = node.place.local.as_usize();
    if node.place.local == rustc_middle::mir::RETURN_PLACE {
        Some(None)
    } else if local > 0 && (local - 1) < arg_count {
        Some(Some(node.place.local.as_u32() as u8 - 1))
    } else {
        None
    }
}
