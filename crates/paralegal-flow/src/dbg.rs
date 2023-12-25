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
use paralegal_spdg::{rustc_portable::DefId, Identifier};

use crate::{
    ir::CallOnlyFlow,
    rust::{mir, TyCtxt},
    utils::{body_name_pls, TyCtxtExt},
    HashMap, HashSet,
};
extern crate dot;

pub fn print_flowistry_matrix<'a: 'tcx, 'tcx, W: std::io::Write>(
    mut out: W,
    matrix: &'a flowistry::infoflow::FlowDomain<'tcx>,
) -> std::io::Result<()> {
    write!(out, "{}", PrintableMatrix(matrix))
}

/// Pretty printing struct for a flowistry result.
pub struct PrintableMatrix<'a>(pub &'a flowistry::infoflow::FlowDomain<'a>);

impl<'a> std::fmt::Display for PrintableMatrix<'a> {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn shortened(mut s: String, i: usize) -> String {
            s.truncate(i);
            s
        }
        let domain = &self.0.col_domain();
        let header_col_width = 10;
        let cell_width = 8;
        write!(out, "{:header_col_width$} |", ' ')?;

        for (_, v) in domain.as_vec().iter_enumerated() {
            write!(out, "{:^cell_width$}", format!("{:?}", v))?
        }
        writeln!(out)?;

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
            writeln!(out)?
        }
        Ok(())
    }
}

pub mod call_only_flow_dot {
    //! Dot graph representation for [`CallOnlyFlow`].
    use std::collections::HashSet;

    use crate::{
        pdg::{CallString, GlobalLocation},
        ir::{CallOnlyFlow},
        rust::mir::{Statement, StatementKind},
        rust::TyCtxt,
        utils::{unique_identifier_for_item, AsFnAndArgs, DfppBodyExt, TyCtxtExt, CallStringExt},
        Either,
    };

    /// `None` encodes the return state of the function
    pub type N = Option<CallString>;
    #[derive(Clone)]
    pub struct E {
        from: N,
        to: N,
        into: To,
    }
    #[derive(Clone, PartialEq, Eq)]
    enum To {
        Ctrl,
        Arg(usize),
    }
    pub struct G<'tcx, 'g, Flow> {
        graph: &'g Flow,
        tcx: TyCtxt<'tcx>,
        detailed: bool,
    }

    impl<'a, 'tcx, 'g> dot::GraphWalk<'a, N, E> for G<'tcx, 'g, CallOnlyFlow> {
        fn nodes(&'a self) -> dot::Nodes<'a, N> {
            self.graph
                .location_dependencies
                .iter()
                .flat_map(|(to, v)| {
                    std::iter::once(*to)
                        .chain(v.ctrl_deps.iter().cloned())
                        .chain(v.input_deps.iter().flat_map(|deps| deps.iter().cloned()))
                })
                .collect::<HashSet<_>>()
                .into_iter()
                .map(Some)
                .chain([None])
                .collect::<Vec<_>>()
                .into()
        }
        fn edges(&'a self) -> dot::Edges<'a, E> {
            self.graph
                .location_dependencies
                .iter()
                .flat_map(|(&to, v)| {
                    v.ctrl_deps
                        .iter()
                        .map(move |&from| E {
                            from: Some(from),
                            to: Some(to),
                            into: To::Ctrl,
                        })
                        .chain(v.input_deps.iter().enumerate().flat_map(move |(i, deps)| {
                            deps.iter().map(move |&from| E {
                                from: Some(from),
                                to: Some(to),
                                into: To::Arg(i),
                            })
                        }))
                })
                .collect::<Vec<_>>()
                .into()
        }
        fn source(&'a self, edge: &E) -> N {
            edge.from
        }
        fn target(&'a self, edge: &E) -> N {
            edge.to
        }
    }

    impl<'a, 'g, 'tcx, Flow> dot::Labeller<'a, N, E> for G<'tcx, 'g, Flow> {
        fn graph_id(&'a self) -> dot::Id<'a> {
            dot::Id::new("g").unwrap()
        }
        fn node_id(&'a self, n: &N) -> dot::Id<'a> {
            if let Some(n) = n {
                dot::Id::new(format!("n{}", n.stable_id())).unwrap()
            } else {
                dot::Id::new("return").unwrap()
            }
        }
        fn node_shape(&'a self, _node: &N) -> Option<dot::LabelText<'a>> {
            Some(dot::LabelText::LabelStr("record".into()))
        }

        fn source_port_position(
            &'a self,
            _e: &E,
        ) -> (Option<dot::Id<'a>>, Option<dot::CompassPoint>) {
            (Some(dot::Id::new("ret").unwrap()), None)
        }

        fn target_port_position(
            &'a self,
            e: &E,
        ) -> (Option<dot::Id<'a>>, Option<dot::CompassPoint>) {
            (
                match e.into {
                    To::Ctrl => Some(dot::Id::new("ctrl").unwrap()),
                    To::Arg(i) => Some(dot::Id::new(format!("a{}", i)).unwrap()),
                },
                None,
            )
        }

        fn node_label(&'a self, n: &N) -> dot::LabelText<'a> {
            use std::fmt::Write;
            let GlobalLocation {
                location: loc,
                function: body_id,
            } = if let Some(n) = n {
                n.leaf()
            } else {
                return dot::LabelText::LabelStr("return".into());
            };
            let body_with_facts = self.tcx.body_for_def_id(body_id).unwrap();
            let body = &body_with_facts.body;
            let write_label = |s: &mut String| -> std::fmt::Result {
                let stmt = if let Some(loc) = loc.as_location() {
                    write!(s, "{{B{}:{}", loc.block.as_usize(), loc.statement_index)?;
                    Some(body.stmt_at_better_err(loc))
                } else {
                    write!(s, "{{Arg")?;
                    None
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
                        Either::Right(term) => {
                            if let Ok((fun, args, _)) = term.as_fn_and_args(self.tcx) {
                                let fun_name = unique_identifier_for_item(self.tcx, fun);
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
                            } else {
                                write!(s, "<ret>")?;
                                term.kind.fmt_head(s)?;
                            }
                        }
                        Either::Left(Statement {
                            kind: StatementKind::Assign(assign),
                            ..
                        }) => {
                            let mut to = String::new();
                            write!(to, "{:?}", assign.1)?;
                            // Chop off the type information (if it exists),
                            // because it makes the dot label invalid
                            if let Some(idx) = to.find([':', '{']) {
                                to.truncate(idx);
                            }
                            write!(s, "<ret>{:?} = {:?}", assign.0, to)?;
                        }
                        Either::Left(_stmt) => {
                            write!(s, "<ret>?")?;
                        }
                    }
                } else {
                    write!(s, "<ret>{:?}", loc)?;
                }
                Ok(())
            };
            let mut s = String::new();
            write_label(&mut s).unwrap();
            dot::LabelText::LabelStr(s.into())
        }

        fn edge_color(&'a self, e: &E) -> Option<dot::LabelText<'a>> {
            (e.into == To::Ctrl).then(|| dot::LabelText::LabelStr("aqua".into()))
        }
    }

    /// Write a dot representation for this `graph` to `out`.
    ///
    /// You can use this function on [`CallOnlyFlow`] or [`GlobalFlowGraph`].
    ///
    /// **Caveat**: the rendering for [`GlobalFlowGraph`] is currently broken,
    /// as it does not show the links into inlined function correctly at the
    /// call site.
    pub fn dump<'tcx, 'g, W: std::io::Write, Flow, N: Clone, E: Clone>(
        tcx: TyCtxt<'tcx>,
        graph: &'g Flow,
        mut out: W,
    ) -> std::io::Result<()>
    where
        for<'a> G<'tcx, 'g, Flow>: dot::GraphWalk<'a, N, E> + dot::Labeller<'a, N, E>,
    {
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

use crate::serializers::{Bodies, BodyProxy};

/// All locations that a body has (helper)
pub fn locations_of_body<'a: 'tcx, 'tcx>(
    body: &'a mir::Body<'tcx>,
) -> impl Iterator<Item = mir::Location> + 'a + 'tcx {
    body.basic_blocks
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
        flow.location_dependencies
            .iter()
            .flat_map(|(l, deps)| {
                std::iter::once(*l).chain(
                    std::iter::once(&deps.ctrl_deps)
                        .chain(deps.input_deps.iter())
                        .flat_map(|s| s.iter().cloned()),
                )
            })
            .map(|l| l.leaf().function)
            .collect::<HashSet<crate::LocalDefId>>()
            .into_iter()
            .map(|bid| {
                (
                    bid.to_def_id(),
                    (
                        Identifier::new(body_name_pls(tcx, bid).name),
                        BodyProxy::from_body_with_normalize(
                            &tcx.body_for_def_id(bid).unwrap().body,
                            tcx,
                        ),
                    ),
                )
            })
            .collect::<HashMap<_, _>>(),
    );

    // We use serde_bare because JSON doesn't allow for non-string hashmap keys,
    // which we use in the CallOnlyFlow
    serde_bare::to_writer(&mut out, &(flow, bodies)).unwrap()
}

/// Read a flow and a set of mentioned `mir::Body`s from the file. Is expected
/// to use JSON serialization.
///
/// The companion function [write_non_transitive_graph_and_body] can be used to
/// create such a file.
pub fn read_non_transitive_graph_and_body<R: std::io::Read>(read: R) -> (CallOnlyFlow, Bodies) {
    serde_bare::from_reader(read).unwrap()
}
