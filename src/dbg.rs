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

use std::borrow::Cow;
use std::collections::HashMap;

use crate::rust::rustc_middle::ty::TyCtxt;
use crate::HashSet;
use flowistry::indexed::impls::LocationDomain;
use flowistry::indexed::{IndexMatrix, IndexedDomain};
use flowistry::infoflow::FlowDomain;
use flowistry::mir::utils::PlaceExt;

use crate::{
    foreign_serializers::SerializableNonTransitiveGraph,
    rust::{mir, rustc_span::symbol::Ident},
    Either, Symbol,
};
extern crate dot;
use crate::ana::{is_real_location, NonTransitiveGraph};

struct DotGraph<'a, 'b, 'tcx> {
    body: &'a mir::Body<'tcx>,
    g: &'a SomeNoneTransitiveGraph<'tcx, 'b, 'a>,
    dom: &'a LocationDomain,
    aliases: Option<&'a flowistry::mir::aliases::Aliases<'b, 'tcx>>,
    tcx: TyCtxt<'tcx>,
}

type N = mir::Location;
type E<'tcx> = (mir::Location, mir::Location, mir::Place<'tcx>);

fn flow_get_row<'b, 'tcx, 'a>(
    g: &'b SomeNoneTransitiveGraph<'tcx, 'a, 'b>,
    from: mir::Location,
) -> &'b flowistry::indexed::IndexMatrix<mir::Place<'tcx>, mir::Location> {
    match g {
        Either::Left(l) => l
            .get(&from)
            .unwrap_or_else(|| panic!("Could not find location {from:?}")),
        Either::Right(f) => f.state_at(from).matrix(),
    }
}

impl<'a, 'b, 'c, 'tcx> dot::GraphWalk<'a, N, E<'tcx>> for DotGraph<'b, 'c, 'tcx> {
    fn nodes(&'a self) -> dot::Nodes<'a, N> {
        self.dom.as_vec().raw.as_slice().into()
    }
    fn edges(&'a self) -> dot::Edges<'a, E<'tcx>> {
        self.nodes()
            .iter()
            .filter(|l| is_real_location(self.body, **l))
            .flat_map(|from| {
                let row = flow_get_row(self.g, *from);
                crate::ana::extract_places(*from, self.body, true)
                    .into_iter()
                    .flat_map(|p|
                        std::iter::once(p).chain(
                        p.refs_in_projection().into_iter().map(|t| mir::Place::from_ref(t.0, self.tcx)).collect::<Vec<_>>().into_iter())
                    )
                    .flat_map(move |p| {
                        let r = row.try_row(p);
                        if r.is_none() {
                            warn!("No row found for place {p:?} at location {from:?}, instruction: {:?}", match self.body.stmt_at(*from) {
                                Either::Left(s) => &s.kind as &dyn std::fmt::Debug,
                                Either::Right(t) => &t.kind as &dyn std::fmt::Debug
                            });
                        }
                        r.into_iter().flat_map(|i| i)
                            .map(move |to| (*from, *to, p))
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

type SomeNoneTransitiveGraph<'tcx, 'a, 'b> = Either<
    NonTransitiveGraph<'tcx>,
    &'b flowistry::infoflow::FlowResults<
        'a,
        'tcx,
        flowistry::infoflow::NonTransitiveFlowDomain<'tcx>,
    >,
>;

impl<'tcx, 'b, 'a, 'c> dot::Labeller<'a, N, E<'tcx>> for DotGraph<'b, 'c, 'tcx> {
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
                    Either::Left(stmt) => format!("[{:?}] {:?}", n.block, stmt.kind),
                    Either::Right(term) => format!("[{:?}] {:?}", n.block, term.kind),
                }
            }
            .into(),
        )
    }
    fn edge_label(&'a self, e: &E<'tcx>) -> dot::LabelText<'a> {
        dot::LabelText::LabelStr(format!("{:?}", e.2).into())
    }
}

pub fn non_transitive_graph_as_dot<'a, 'tcx, W: std::io::Write>(
    out: &mut W,
    body: &mir::Body<'tcx>,
    g: &SomeNoneTransitiveGraph<'tcx, 'a, '_>,
    dom: &LocationDomain,
    aliases: Option<&flowistry::mir::aliases::Aliases<'a, 'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> std::io::Result<()> {
    dot::render(
        &DotGraph {
            body,
            g,
            dom,
            aliases,
            tcx,
        },
        out,
    )
}

use crate::foreign_serializers::{BodyProxy, NonTransitiveGraphProxy};

pub fn locations_of_body<'a>(body: &'a mir::Body) -> impl Iterator<Item = mir::Location> + 'a {
    body.basic_blocks()
        .iter_enumerated()
        .flat_map(|(block, dat)| {
            (0..=dat.statements.len()).map(move |statement_index| mir::Location {
                block,
                statement_index,
            })
        })
}

pub fn dump_non_transitive_graph_and_body<'a, 'tcx>(
    id: Ident,
    body: &mir::Body<'tcx>,
    g: &SomeNoneTransitiveGraph<'tcx, 'a, '_>,
    dom: &LocationDomain,
    tcx: TyCtxt<'tcx>,
) {
    serde_json::to_writer(
        &mut std::fs::OpenOptions::new()
            .truncate(true)
            .create(true)
            .write(true)
            .open(format!("{}.ntgb.json", id.name.as_str()))
            .unwrap(),
        &match g {
            Either::Left(f) => (BodyProxy::from(body), NonTransitiveGraphProxy::from(f)),
            Either::Right(g) => (
                BodyProxy::from_body_with_normalize(body, &g.analysis.aliases, tcx),
                NonTransitiveGraphProxy::from(
                    &locations_of_body(body)
                        .map(|l| (l, g.state_at(l).matrix().clone()))
                        .collect::<HashMap<_, _>>(),
                ),
            ),
        },
    )
    .unwrap()
}

pub fn read_non_transitive_graph_and_body(
    id: Symbol,
) -> (
    Vec<(mir::Location, String, HashSet<Symbol>)>,
    SerializableNonTransitiveGraph,
) {
    let deser: (BodyProxy, NonTransitiveGraphProxy) = serde_json::from_reader(
        &mut std::fs::File::open(format!("{}.ntgb.json", id.as_str())).unwrap(),
    )
    .unwrap();
    (deser.0 .0, deser.1.into())
}
