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
use crate::rust::mir;

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
