//! Display SPDGs as dot graphs

use crate::{GlobalEdge, InstructionKind, Node, ProgramDescription};
use dot::{CompassPoint, Edges, Id, LabelText, Nodes};
use flowistry_pdg::rustc_portable::LocalDefId;
use flowistry_pdg::{CallString, RichLocation};

use petgraph::prelude::EdgeRef;
use petgraph::visit::{IntoNodeReferences, NodeRef};
use std::collections::HashMap;

struct DotPrintableProgramDescription<'d> {
    spdg: &'d ProgramDescription,
    call_sites: HashMap<CallString, (LocalDefId, Vec<Node>)>,
    selected_controllers: Vec<LocalDefId>,
}

impl<'d> DotPrintableProgramDescription<'d> {
    pub fn new_for_selection(
        spdg: &'d ProgramDescription,
        mut selector: impl FnMut(LocalDefId) -> bool,
    ) -> Self {
        let selected_controllers: Vec<_> = spdg
            .controllers
            .keys()
            .copied()
            .filter(|l| selector(*l))
            .collect();
        let mut call_sites = HashMap::new();
        for c in selected_controllers.iter() {
            let ctrl = &spdg.controllers[c];
            for w in ctrl.graph.node_references() {
                let e = call_sites
                    .entry(w.weight().at)
                    .or_insert_with(|| (*c, vec![]));
                e.1.push(w.id());
            }
        }
        Self {
            call_sites,
            spdg,
            selected_controllers,
        }
    }

    fn format_call_string(&self, call_string: CallString) -> String {
        use std::fmt::Write;
        let mut s = String::new();
        for loc in call_string.iter_from_root() {
            if !s.is_empty() {
                s.push('@');
            }
            match loc.location {
                RichLocation::Location(l) => {
                    write!(s, "bb{}[{}]", l.block.index(), l.statement_index).unwrap()
                }
                RichLocation::End => s.push_str("end"),
                RichLocation::Start => s.push_str("start"),
            }
        }
        s
    }
}

impl<'a, 'd> dot::GraphWalk<'a, CallString, GlobalEdge> for DotPrintableProgramDescription<'d> {
    fn nodes(&'a self) -> Nodes<'a, CallString> {
        self.call_sites.keys().copied().collect::<Vec<_>>().into()
    }
    fn edges(&'a self) -> Edges<'a, GlobalEdge> {
        self.selected_controllers
            .iter()
            .flat_map(|&controller_id| {
                let ctrl = &self.spdg.controllers[&controller_id];
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
        let instruction = &self.spdg.instruction_info[&n.leaf()];

        let write_label = || {
            use std::fmt::Write;
            let mut s = String::new();

            write!(s, "{}|", self.format_call_string(*n))?;

            match instruction.kind {
                InstructionKind::Statement => s.push('S'),
                InstructionKind::FunctionCall(function) => {
                    let info = &self.spdg.def_info[&function.id];
                    write!(s, "{}", info.name)?
                }
                InstructionKind::Terminator => s.push('T'),
                InstructionKind::Start => {
                    s.push('*');
                }
                InstructionKind::Return => s.push_str("end"),
            };

            for &n in nodes {
                let weight = ctrl.graph.node_weight(n).unwrap();
                let markers = ctrl.markers.get(&n).into_iter().flatten();
                let type_markers = ctrl
                    .type_assigns
                    .get(&n)
                    .into_iter()
                    .flat_map(|typ| typ.0.iter().flat_map(|t| &self.spdg.type_info[t].markers));
                let mut all_markers = markers.chain(type_markers).copied().peekable();
                let write_id_and_desc = |s: &mut String| {
                    let idx = n.index();
                    let desc = weight.description.replace('<', "&lt;").replace('>', "&gt;");
                    write!(s, "<p{idx}> ({idx}) {desc}")
                };
                s.push('|');
                if all_markers.peek().is_some() {
                    s.push('{');
                    write_id_and_desc(&mut s)?;
                    for m in all_markers {
                        write!(s, "| {m}")?;
                    }
                    s.push('}');
                } else {
                    write_id_and_desc(&mut s)?;
                }
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

/// Dump all SPDGs in a single dot expression
pub fn dump<W: std::io::Write>(spdg: &ProgramDescription, out: W) -> std::io::Result<()> {
    dump_for_selection(spdg, out, |_| true)
}

/// Dump the SPDG for one select controller in dot format
pub fn dump_for_controller(
    spdg: &ProgramDescription,
    out: impl std::io::Write,
    controller_id: LocalDefId,
) -> std::io::Result<()> {
    let mut found = false;
    dump_for_selection(spdg, out, |l| {
        let is_target = l == controller_id;
        if is_target {
            found = true;
        }
        is_target
    })?;
    assert!(
        found,
        "No such controller was found in the program description"
    );
    Ok(())
}

/// Dump a selection of controllers into a dot expression.
pub fn dump_for_selection(
    spdg: &ProgramDescription,
    mut out: impl std::io::Write,
    selector: impl FnMut(LocalDefId) -> bool,
) -> std::io::Result<()> {
    let printable = DotPrintableProgramDescription::new_for_selection(spdg, selector);
    dot::render(&printable, &mut out)
}
