//! Helpers for debugging
//! 
//! Defines pretty printers and dot graph output. 
//! 
//! Often times the pretty printers wrappers around references to graph structs,
//! like [PrintableMatrix]. These wrappers have
//! `Debug` and/or `Display` implementations so that you can flexibly print them
//! to stdout, a file or a log statement. Some take additional information (such
//! as [TyCtxt]) to get contextual information that is used to make the output
//! more useful.
use flowistry::indexed::IndexedDomain;

use crate::{
    ana::{CallOnlyFlow, GlobalFlowGraph, GlobalLocation},
    rust::{
        mir::{self, Place},
        TyCtxt,
    },
    utils::{self, is_real_location},
    HashMap, HashSet, IsGlobalLocation,
};
extern crate dot;

pub fn print_flowistry_matrix<W: std::io::Write>(
    mut out: W,
    matrix: &crate::sah::Matrix,
) -> std::io::Result<()> {
    write!(out, "{}", PrintableMatrix(matrix))
}

/// Pretty printing struct for a flowistry result.
pub struct PrintableMatrix<'a>(pub &'a crate::sah::Matrix<'a>);

impl<'a> std::fmt::Display for PrintableMatrix<'a> {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn shortened(mut s: String, i: usize) -> String {
            s.truncate(i);
            s
        }
        let domain = &self.0.col_domain;
        let header_col_width = 10;
        let cell_width = 8;
        write!(out, "{:header_col_width$} |", ' ')?;

        for (_, v) in domain.as_vec().iter_enumerated() {
            write!(out, "{:^cell_width$}", format!("{:?}", v))?
        }
        writeln!(out, "")?;

        for (v, r) in self.0.rows() {
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
}

pub mod call_only_flow_dot {
    //! Dot graph representation for [`CallOnlyFlow`].
    use std::collections::HashSet;

    use crate::{
        ana::{CallOnlyFlow, GlobalLocation, IsGlobalLocation},
        rust::ty::TyCtxt,
        utils::AsFnAndArgs,
        Either,
    };

    type N<'g> = GlobalLocation<'g>;
    #[derive(Clone)]
    struct E<'g> {
        from: N<'g>,
        to: N<'g>,
        into: To,
    }
    #[derive(Clone)]
    enum To {
        Ctrl,
        Arg(usize),
    }
    struct G<'tcx, 'g> {
        graph: &'g CallOnlyFlow<'g>,
        tcx: TyCtxt<'tcx>,
        detailed: bool,
    }

    impl<'a, 'tcx, 'g> dot::GraphWalk<'a, N<'g>, E<'g>> for G<'tcx, 'g> {
        fn nodes(&'a self) -> dot::Nodes<'a, N<'g>> {
            self.graph
                .iter()
                .flat_map(|(to, v)| {
                    std::iter::once(*to)
                        .chain(v.ctrl_deps.iter().cloned())
                        .chain(v.input_deps.iter().flat_map(|deps| deps.iter().cloned()))
                })
                .collect::<HashSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
                .into()
        }
        fn edges(&'a self) -> dot::Edges<'a, E<'g>> {
            self.graph
                .iter()
                .flat_map(|(&to, v)| {
                    v.ctrl_deps
                        .iter()
                        .map(move |&from| E {
                            from,
                            to,
                            into: To::Ctrl,
                        })
                        .chain(v.input_deps.iter().enumerate().flat_map(move |(i, deps)| {
                            deps.iter().map(move |&from| E {
                                from,
                                to,
                                into: To::Arg(i),
                            })
                        }))
                })
                .collect::<Vec<_>>()
                .into()
        }
        fn source(&'a self, edge: &E<'g>) -> N<'g> {
            edge.from
        }
        fn target(&'a self, edge: &E<'g>) -> N<'g> {
            edge.to
        }
    }

    impl<'a, 'g, 'tcx> dot::Labeller<'a, N<'g>, E<'g>> for G<'tcx, 'g> {
        fn graph_id(&'a self) -> dot::Id<'a> {
            dot::Id::new("g").unwrap()
        }
        fn node_id(&'a self, n: &N<'g>) -> dot::Id<'a> {
            dot::Id::new(format!("n{}", n.stable_id())).unwrap()
        }
        fn node_shape(&'a self, _node: &N<'g>) -> Option<dot::LabelText<'a>> {
            Some(dot::LabelText::LabelStr("record".into()))
        }

        fn source_port_position(
            &'a self,
            _e: &E<'g>,
        ) -> (Option<dot::Id<'a>>, Option<dot::CompassPoint>) {
            (Some(dot::Id::new("ret").unwrap()), None)
        }

        fn target_port_position(
            &'a self,
            e: &E<'g>,
        ) -> (Option<dot::Id<'a>>, Option<dot::CompassPoint>) {
            (
                Some(
                    match e.into {
                        To::Ctrl => dot::Id::new("ctrl"),
                        To::Arg(i) => dot::Id::new(format!("a{}", i)),
                    }
                    .unwrap(),
                ),
                None,
            )
        }

        fn node_label(&'a self, n: &N<'g>) -> dot::LabelText<'a> {
            use std::fmt::Write;
            let (loc, body_id) = n.innermost_location_and_body();
            let body_with_facts = flowistry::mir::borrowck_facts::get_body_with_borrowck_facts(
                self.tcx,
                self.tcx.hir().body_owner_def_id(body_id),
            );
            let body = &body_with_facts.body;
            let write_label = |s: &mut String| -> std::fmt::Result {
                write!(s, "{{B{}:{}", loc.block.as_usize(), loc.statement_index)?;
                if self.detailed {
                    let mut locs = n.iter().collect::<Vec<_>>();
                    locs.pop();
                    locs.reverse();
                    for l in locs.into_iter() {
                        write!(
                            s,
                            "@{:?}:{}",
                            l.location().block,
                            l.location().statement_index
                        )?;
                    }
                };
                let stmt = if !crate::utils::is_real_location(&body, loc) {
                    None
                } else {
                    Some(body.stmt_at(loc))
                };
                let typ = if let Some(ref stmt) = stmt {
                    if stmt.is_left() {
                        "S"
                    } else {
                        "T"
                    }
                } else {
                    "A"
                };
                write!(s, "|{typ}}}|")?;
                if let Some(stmt) = stmt {
                    match stmt {
                        Either::Left(_stmt) => {
                            unimplemented!()
                        }
                        Either::Right(term) => {
                            let (fun, args, _) = term.as_fn_and_args().unwrap();
                            let fun_name = self.tcx.item_name(fun);
                            write!(s, "{{{{")?;
                            for (i, arg) in args.iter().enumerate() {
                                write!(s, "<a{}>", i)?;
                                match arg {
                                    Some(a) if self.detailed => write!(s, "{:?}", a),
                                    _ => write!(s, "{}", i),
                                }?;
                                write!(s, "|")?;
                            }
                            write!(s, "C}}|<ret>{fun_name}}}")?;
                        }
                    }
                } else {
                    write!(
                        s,
                        "<ret>{}",
                        flowistry::mir::utils::location_to_string(loc, body)
                    )?;
                }
                Ok(())
            };
            let mut s = String::new();
            write_label(&mut s).unwrap();
            dot::LabelText::LabelStr(s.into())
        }
    }

    /// Write a dot representation for this `graph` to `out`.
    pub fn dump<W: std::io::Write>(
        tcx: TyCtxt,
        graph: &CallOnlyFlow,
        mut out: W,
    ) -> std::io::Result<()> {
        dot::render(
            &G {
                graph,
                tcx,
                detailed: false,
            },
            &mut out,
        )
    }
}

pub struct PrintableGranularFlow<'a, 'g, 'tcx> {
    pub flow: &'a GlobalFlowGraph<'tcx, 'g>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'g> GlobalLocation<'g> {
    pub fn iter(self) -> impl Iterator<Item = GlobalLocation<'g>> {
        std::iter::successors(Some(self), |l| l.next().cloned())
    }
}

/// Formatting for global locations that works independent of whether it is an
/// interned or inlined location.
fn format_global_location<T: IsGlobalLocation>(
    t: &T,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let mut v = std::iter::successors(Some(t), |l| l.next()).collect::<Vec<_>>();
    v.reverse();
    let mut is_first = true;
    while let Some(next) = v.pop() {
        if is_first {
            is_first = false;
        } else {
            write!(f, "@")?;
        }
        write!(
            f,
            "{:?}[{}]",
            next.location().block,
            next.location().statement_index
        )?;
    }
    Ok(())
}

impl<'g> std::fmt::Display for GlobalLocation<'g> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        format_global_location(self, f)
    }
}

/// A [`crate::ana::GlobalDepMatrix`] that can be `Display`ed with
/// an indent.
pub struct PrintableDependencyMatrix<'a, 'g, 'tcx>(
    &'a crate::ana::GlobalDepMatrix<'tcx, 'g>,
    usize,
);

impl<'a, 'g, 'tcx> PrintableDependencyMatrix<'a, 'g, 'tcx> {
    pub fn new(map: &'a HashMap<Place<'tcx>, HashSet<GlobalLocation<'g>>>, indent: usize) -> Self {
        Self(map, indent)
    }
}

impl<'a, 'g, 'tcx> std::fmt::Display for PrintableDependencyMatrix<'a, 'g, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        format_dependency_matrix(f, self.0.iter().map(|(k, v)| (*k, false, v)), self.1)
    }
}

/// Helper function for the `Display` implementation on
/// [`PrintableDependencyMatrix`](./struct.PrintableDependencyMatrix.html)
pub fn format_dependency_matrix<
    'tcx,
    'g,
    I: IntoIterator<Item = (Place<'tcx>, bool, &'g HashSet<GlobalLocation<'g>>)>,
>(
    f: &mut std::fmt::Formatter<'_>,
    it: I,
    indent: usize,
) -> std::fmt::Result {
    for (place, read, deps) in it {
        write!(
            f,
            "{:indent$}{}{:?} -> ",
            "",
            if read { "> " } else { "" },
            place
        )?;
        let mut is_first = true;
        write!(f, "{{")?;
        for dep in deps.iter().cloned() {
            if !is_first {
                write!(f, ", ")?;
            } else {
                is_first = true;
            }
            write!(f, "{dep}")?;
        }
        writeln!(f, "}}")?;
    }
    Ok(())
}

impl<'a, 'tcx, 'g> std::fmt::Debug for PrintableGranularFlow<'a, 'g, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (loc, deps) in self.flow.location_states.iter() {
            write!(f, "  {}", loc)?;
            let (inner_location, inner_body) = loc.innermost_location_and_body();
            let body = flowistry::mir::borrowck_facts::get_body_with_borrowck_facts(
                self.tcx,
                self.tcx.hir().body_owner_def_id(inner_body),
            );
            let places_read = if !is_real_location(&body.body, inner_location) {
                write!(f, " is argument {}", inner_location.statement_index - 1)?;
                HashSet::new()
            } else {
                utils::places_read(inner_location, &body.body.stmt_at(inner_location)).collect()
            };
            writeln!(f, "")?;
            let empty_set = HashSet::new();
            format_dependency_matrix(
                f,
                places_read
                    .iter()
                    .cloned()
                    .map(|p| (p, true, deps.get(&p).unwrap_or(&empty_set)))
                    .chain(
                        deps.iter()
                            .filter(|k| !places_read.contains(k.0))
                            .map(|(p, deps)| (*p, false, deps)),
                    ),
                4,
            )?;
        }
        Ok(())
    }
}

use crate::serializers::{Bodies, BodyProxy, SerializableCallOnlyFlow};

/// All locations that a body has (helper)
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

/// Write this `flow` to `out` using a JSON serializer. The companion function
/// for reading the graph back in is
/// [read_non_transitive_graph_and_body].
pub fn write_non_transitive_graph_and_body<W: std::io::Write>(
    tcx: TyCtxt,
    flow: &CallOnlyFlow,
    mut out: W,
) {
    let bodies = Bodies(
        flow.iter()
            .flat_map(|(l, deps)| {
                std::iter::once(*l).chain(
                    std::iter::once(&deps.ctrl_deps)
                        .chain(deps.input_deps.iter())
                        .flat_map(|s| s.iter().cloned()),
                )
            })
            .map(|l| l.function())
            .collect::<HashSet<crate::rust::hir::BodyId>>()
            .into_iter()
            .map(|bid| {
                (
                    bid,
                    BodyProxy::from_body_with_normalize(
                        &flowistry::mir::borrowck_facts::get_body_with_borrowck_facts(
                            tcx,
                            tcx.hir().body_owner_def_id(bid),
                        )
                        .body,
                        tcx,
                    ),
                )
            })
            .collect::<HashMap<_, _>>(),
    );
    serde_json::to_writer(
        &mut out,
        &(
            crate::serializers::SerializableCallOnlyFlow::from(flow),
            bodies,
        ),
    )
    .unwrap()
}

/// Read a flow and a set of mentioned `mir::Body`s from the file. Is expected
/// to use JSON serialization.
/// 
/// The companion function [write_non_transitive_graph_and_body] can be used to
/// create such a file.
pub fn read_non_transitive_graph_and_body<R: std::io::Read>(
    read: R,
) -> (SerializableCallOnlyFlow, Bodies) {
    serde_json::from_reader(read).unwrap()
}
