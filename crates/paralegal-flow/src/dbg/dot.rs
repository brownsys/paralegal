use crate::pdg::CallString;
use crate::TyCtxt;
use dot::{Edges, Id, LabelText, Nodes};
use flowistry::pdg::graph::DepGraph;
use paralegal_spdg::Node;
use petgraph::graph::EdgeIndex;
use std::io::Write;

/// Unlike printing the SPDG this does not group by call site
struct DotPrintableFlowistryPDG<'tcx, 'g> {
    pdg: &'g DepGraph<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'g, 'tcx, 'a> dot::GraphWalk<'a, Node, EdgeIndex> for DotPrintableFlowistryPDG<'tcx, 'g> {
    fn nodes(&'a self) -> Nodes<'a, Node> {
        self.pdg.graph.node_indices().collect::<Vec<_>>().into()
    }

    fn edges(&'a self) -> Edges<'a, EdgeIndex> {
        self.pdg.graph.edge_indices().collect::<Vec<_>>().into()
    }

    fn source(&'a self, edge: &EdgeIndex) -> Node {
        self.pdg.graph.edge_endpoints(*edge).unwrap().0
    }

    fn target(&'a self, edge: &EdgeIndex) -> Node {
        self.pdg.graph.edge_endpoints(*edge).unwrap().1
    }
}

impl<'a, 'tcx, 'g> dot::Labeller<'a, Node, EdgeIndex> for DotPrintableFlowistryPDG<'tcx, 'g> {
    fn graph_id(&'a self) -> Id<'a> {
        Id::new("g").unwrap()
    }

    fn node_id(&'a self, n: &Node) -> Id<'a> {
        Id::new(format!("n{}", n.index())).unwrap()
    }

    fn node_shape(&'a self, _node: &Node) -> Option<LabelText<'a>> {
        Some(LabelText::LabelStr("record".into()))
    }

    fn node_label(&'a self, n: &Node) -> LabelText<'a> {
        use std::fmt::Write;
        let weight = self.pdg.graph.node_weight(*n).unwrap();

        let mut label = format!("{:?}", weight.place)
            .replace("<", "&lt;")
            .replace(">", "&gt;");

        write!(label, "  {}", weight.at.to_string().replace("←", "@")).unwrap();

        LabelText::LabelStr(label.into())
    }
}

pub fn dump<'tcx>(
    pdg: &DepGraph<'tcx>,
    tcx: TyCtxt<'tcx>,
    mut out: impl Write,
) -> std::io::Result<()> {
    dot::render(&DotPrintableFlowistryPDG { pdg, tcx }, &mut out)
}
