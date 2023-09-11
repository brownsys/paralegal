//! This crate is the engine of the property checker. It consumes
//! a PDG output by `dfpp` and checks user-defined properties on the PDG.
//!
//! *Note:* This crate defines both the interface to the property checkers
//! (via [`Context`]) and the implementation of the engine (via [`cli`]). A
//! future version of this crate should ideally separate those out so
//! property checkers do not need to depend on the checker implementation.

#![warn(missing_docs)]

use anyhow::Result;
use dfgraph::ProgramDescription;
use std::env;
use std::fs::File;
use std::sync::Arc;

pub use self::{context::Context, flows_to::CtrlFlowsTo};
pub use dfgraph;

mod context;
mod flows_to;
#[cfg(test)]
mod test_utils;

/// Top-level entry point into the property checker engine.
///
/// A user-defined checker should call this function in its `main`,
/// and provide a callback that receives the loaded [`Context`].
pub fn cli(cb: impl FnOnce(Arc<Context>)) {
    let inner = move || -> Result<()> {
        simple_logger::init_with_env().unwrap();

        let mut args = env::args().skip(1);
        let graph_path = args.next().unwrap();

        let desc = {
            let mut f = File::open(graph_path)?;
            serde_json::from_reader::<_, ProgramDescription>(&mut f)?
        };
        let cx = Arc::new(Context::new(desc));
        cb(cx);

        Ok(())
    };
    inner().unwrap();
}
