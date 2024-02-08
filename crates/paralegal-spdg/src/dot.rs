use crate::{GlobalEdge, InstructionInfo, Node, ProgramDescription};
use dot::{CompassPoint, Edges, Id, LabelText, Nodes};
use flowistry_pdg::rustc_portable::LocalDefId;
use flowistry_pdg::CallString;

use petgraph::prelude::EdgeRef;
use petgraph::visit::{IntoNodeReferences, NodeRef};
use std::collections::HashMap;

struct DotPrintableProgramDescription<'d> {
    spdg: &'d ProgramDescription,
    call_sites: HashMap<CallString, (LocalDefId, Vec<Node>)>,
}

impl<'d> DotPrintableProgramDescription<'d> {
    pub fn new(spdg: &'d ProgramDescription) -> Self {
        let mut call_sites = HashMap::new();
        for (c, ctrl) in spdg.controllers.iter() {
            for w in ctrl.graph.node_references() {
                let e = call_sites
                    .entry(w.weight().at)
                    .or_insert_with(|| (*c, vec![]));
                e.1.push(w.id());
            }
        }
        Self { call_sites, spdg }
    }
}

impl<'a, 'd> dot::GraphWalk<'a, CallString, GlobalEdge> for DotPrintableProgramDescription<'d> {
    fn nodes(&'a self) -> Nodes<'a, CallString> {
        self.call_sites.keys().copied().collect::<Vec<_>>().into()
    }
    fn edges(&'a self) -> Edges<'a, GlobalEdge> {
        self.spdg
            .controllers
            .iter()
            .flat_map(|(&controller_id, ctrl)| {
                ctrl.graph.edge_references().map(move |edge| GlobalEdge {
                    controller_id,
                    index: edge.id(),
                })
            })
            .collect::<Vec<_>>()
            .into()
    }

    fn source(&'a self, edge: &GlobalEdge) -> CallString {
        let ctrl = &self.spdg.controllers[&edge.controller_id].graph;
        let (from, _) = ctrl.edge_endpoints(edge.index).unwrap();
        ctrl.node_weight(from).unwrap().at
    }

    fn target(&'a self, edge: &GlobalEdge) -> CallString {
        let ctrl = &self.spdg.controllers[&edge.controller_id].graph;
        let (_, to) = ctrl.edge_endpoints(edge.index).unwrap();
        ctrl.node_weight(to).unwrap().at
    }
}

impl<'a, 'd> dot::Labeller<'a, CallString, GlobalEdge> for DotPrintableProgramDescription<'d> {
    fn graph_id(&'a self) -> Id<'a> {
        Id::new("g").unwrap()
    }
    fn node_id(&'a self, n: &CallString) -> Id<'a> {
        Id::new(format!("n{}", n.stable_id())).unwrap()
    }

    fn node_shape(&'a self, _node: &CallString) -> Option<LabelText<'a>> {
        Some(LabelText::LabelStr("record".into()))
    }

    fn node_label(&'a self, n: &CallString) -> LabelText<'a> {
        let (ctrl_id, nodes) = &self.call_sites[n];
        let ctrl = &self.spdg.controllers[ctrl_id];
        let instruction = self.spdg.instruction_info[&n.leaf()];

        let write_label = || {
            use std::fmt::Write;
            let mut s = String::new();

            write!(s, "{}|", n.to_string().replace('←', "@"))?;

            match instruction {
                InstructionInfo::Statement => s.push('S'),
                InstructionInfo::FunctionCall(function) => {
                    let info = &self.spdg.def_info[&function.id];
                    write!(s, "{}", info.name)?
                }
                InstructionInfo::Terminator => s.push('T'),
                InstructionInfo::Start => {
                    s.push('*');
                }
                InstructionInfo::Return => s.push_str("end"),
            };

            for n in nodes {
                let weight = ctrl.graph.node_weight(*n).unwrap();
                write!(
                    s,
                    "|<p{}>{}",
                    n.index(),
                    weight.description.replace('<', "&lt;").replace('>', "&gt;")
                )?;
            }

            Ok::<_, std::fmt::Error>(s)
        };

        LabelText::LabelStr(write_label().unwrap().into())
    }

    fn edge_color(&'a self, e: &GlobalEdge) -> Option<dot::LabelText<'a>> {
        let weight = self.spdg.controllers[&e.controller_id]
            .graph
            .edge_weight(e.index)
            .unwrap();
        weight
            .is_control()
            .then(|| LabelText::LabelStr("aqua".into()))
    }

    fn source_port_position(
        &'a self,
        edge: &GlobalEdge,
    ) -> (Option<dot::Id<'a>>, Option<dot::CompassPoint>) {
        let ctrl = &self.spdg.controllers[&edge.controller_id].graph;
        let (from, _) = ctrl.edge_endpoints(edge.index).unwrap();
        (Some(Id::new(format!("p{}", from.index())).unwrap()), None)
    }

    fn target_port_position(&'a self, edge: &GlobalEdge) -> (Option<Id<'a>>, Option<CompassPoint>) {
        let ctrl = &self.spdg.controllers[&edge.controller_id].graph;
        let (_, to) = ctrl.edge_endpoints(edge.index).unwrap();
        (Some(Id::new(format!("p{}", to.index())).unwrap()), None)
    }
}

pub fn dump<W: std::io::Write>(spdg: &ProgramDescription, mut out: W) -> std::io::Result<()> {
    let printable = DotPrintableProgramDescription::new(spdg);
    dot::render(&printable, &mut out)
}
