pub fn print_flowistry_matrix<W: std::io::Write>(
    mut out: W,
    matrix: &crate::sah::Matrix,
) -> std::io::Result<()> {
    fn shortened(mut s: String, i: usize) -> String {
        s.truncate(i);
        s
    }
    use flowistry::indexed::IndexedDomain;
    let domain = &matrix.col_domain;
    let header_col_width = 10;
    let cell_width = 8;
    write!(out, "{:header_col_width$} |", ' ')?;

    for (_, v) in domain.as_vec().iter_enumerated() {
        write!(out, "{:^cell_width$}", format!("{:?}", v))?
    }
    writeln!(out, "")?;

    for (v, r) in matrix.rows() {
        write!(
            out,
            "{:header_col_width$} |",
            shortened(format!("{:?}", v), header_col_width)
        )?;
        for (i, _) in domain.as_vec().iter_enumerated() {
            write!(
                out,
                "{:^cell_width$}",
                if r.contains(i) { "×" } else { " " }
            )?
        }
        writeln!(out, "")?
    }
    Ok(())
}

use flowistry::indexed::IndexMatrix;

use crate::{
    rust::{mir, rustc_span::symbol::Ident},
    Either, Symbol, foreign_serializers::SerializableNonTransitiveGraph,
};
extern crate dot;
use crate::ana::NonTransitiveGraph;

struct DotGraph<'a, 'tcx> {
    body: &'a mir::Body<'tcx>,
    g: &'a NonTransitiveGraph<'tcx>,
}

type N = mir::Location;
type E<'tcx> = (mir::Location, mir::Location, mir::Place<'tcx>);

impl<'a, 'b, 'tcx> dot::GraphWalk<'a, N, E<'tcx>> for DotGraph<'b, 'tcx> {
    fn nodes(&'a self) -> dot::Nodes<'a, N> {
        self.g.keys().cloned().collect::<Vec<_>>().into()
    }
    fn edges(&'a self) -> dot::Edges<'a, E<'tcx>> {
        self.g
            .iter()
            .flat_map(|(from, matrix)| {
                matrix.rows().flat_map(move |(r, s)| {
                    s.iter()
                        .map(move |to| (*from, *to, r))
                        .collect::<Vec<_>>()
                        .into_iter()
                })
            })
            .collect::<Vec<_>>()
            .into()
    }
    fn source(&'a self, edge: &E<'tcx>) -> N {
        edge.1
    }
    fn target(&'a self, edge: &E<'tcx>) -> N {
        edge.0
    }
}

impl<'tcx, 'b, 'a> dot::Labeller<'a, N, E<'tcx>> for DotGraph<'b, 'tcx> {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("g").unwrap()
    }
    fn node_id(&'a self, n: &N) -> dot::Id<'a> {
        dot::Id::new(format!("{n:?}").replace(['[', ']'], "_").to_string()).unwrap()
    }
    fn node_label(&'a self, n: &N) -> dot::LabelText<'a> {
        use crate::Either;
        dot::LabelText::LabelStr(
            if !crate::ana::is_real_location(self.body, *n) {
                format!(
                    "Argument {}",
                    flowistry::mir::utils::location_to_string(*n, self.body)
                )
            } else {
                match self.body.stmt_at(*n) {
                    Either::Left(stmt) => format!("{:?}", stmt.kind),
                    Either::Right(term) => format!("{:?}", term.kind),
                }
            }
            .into(),
        )
    }
    fn edge_label(&'a self, e: &E<'tcx>) -> dot::LabelText<'a> {
        dot::LabelText::LabelStr(format!("{:?}", e.2).into())
    }
}

pub fn non_transitive_graph_as_dot<'tcx, W: std::io::Write>(
    out: &mut W,
    body: &mir::Body<'tcx>,
    g: &NonTransitiveGraph<'tcx>,
) -> std::io::Result<()> {
    dot::render(&DotGraph { body, g }, out)
}

use crate::foreign_serializers::{BodyProxy, NonTransitiveGraphProxy};

pub fn dump_non_transitive_graph_and_body<'tcx>(
    id: Ident,
    body: &mir::Body<'tcx>,
    g: &NonTransitiveGraph<'tcx>,
) {
    serde_json::to_writer(
        &mut std::fs::OpenOptions::new()
            .truncate(true)
            .create(true)
            .write(true)
            .open(format!("{}.ntgb.json", id.name.as_str()))
            .unwrap(),
        &(BodyProxy::from(body), NonTransitiveGraphProxy::from(g))
    )
    .unwrap()
}

pub fn read_non_transitive_graph_and_body(
    id: Symbol,
) -> (Vec<(mir::Location, String)>, SerializableNonTransitiveGraph) {
    let deser: (BodyProxy, NonTransitiveGraphProxy) = serde_json::from_reader(
        &mut std::fs::File::open(format!("{}.ntgb.json", id.as_str())).unwrap(),
    )
    .unwrap();
    (deser.0.0, deser.1.into())
}
