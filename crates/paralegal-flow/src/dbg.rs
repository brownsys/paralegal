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
use crate::{
    rust::{mir, TyCtxt},
    utils::TyCtxtExt,
};

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
