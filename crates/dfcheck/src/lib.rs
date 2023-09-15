//! This crate is the engine of the property checker. It consumes a PDG output
//! by `dfpp` and checks user-defined properties on the PDG.
//!
//! We also define a programmatic way to invoke the graph generator via
//! [`SPDGGenCommand`]. The most common workflow (relies on `dfpp` having been
//! installed globally) is
//!
//! ```ignore
//! let ctx = SPDGGenCommand::global()
//!     .run("project/dir/to/analyze")?
//!     .build_context()?;
//! my_property(ctx)
//! ```
//!
//! If you do not wish to run the graph generation programmatically you can also
//! point your analysis at the graph file manually with [`GraphLocation::std`]
//! (uses the default name for the graph file in the specified directory) or
//! [`GraphLocation::custom`] for a completely custom graph file location. To
//! run your property use [`GraphLocation::build_context`].
//!
//! *Note:* This crate defines both the interface to the property checkers (via
//! [`Context`]) and the implementation of the engine (via
//! [`GraphLocation::build_context`]). A future version of this crate should
//! ideally separate those out so property checkers do not need to depend on the
//! checker implementation.

#![warn(missing_docs)]

use anyhow::{ensure, Result};
pub use dfgraph;
use dfgraph::ProgramDescription;
use std::{
    fs::File,
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
};

mod context;
mod flows_to;
#[cfg(test)]
mod test_utils;

pub use self::{context::*, flows_to::CtrlFlowsTo};

/// Configuration of the `cargo dfpp` command.
///
/// Takes care of passing the right kinds of arguments to produce the
/// [`ProgramDescription`] graph that the properties consume.
///
/// Construct the command with [`Self::global`] or [`Self::custom`], customize
/// it further with [`Self::get_command`] and once you are ready, execute it
/// with [`Self::run`].
#[derive(Debug)]
pub struct SPDGGenCommand(Command);

impl SPDGGenCommand {
    /// Use a global installation of `dfpp` via `cargo dfpp`.
    pub fn global() -> Self {
        let mut cmd = Command::new("cargo");
        cmd.arg("dfpp");
        Self::custom(cmd)
    }

    /// Use a custom binary or base invocation as command.
    pub fn custom(mut cmd: Command) -> Self {
        cmd.args(&["--dump", "serialized-flow-graph"]);
        Self(cmd)
    }

    /// Mutably borrow the command to perform further customization.
    pub fn get_command(&mut self) -> &mut Command {
        &mut self.0
    }

    /// Consume the created command and execute it in the specified directory.
    ///
    /// Errors if executing the underlying [`Command`] fails or if it does not
    /// terminate successfully.
    ///
    /// To run yor properties on the results see [`GraphLocation`].
    pub fn run(mut self, dir: impl AsRef<Path>) -> Result<GraphLocation> {
        let status = self.0.current_dir(dir.as_ref()).status()?;
        ensure!(status.success(), "Compilation failed");
        Ok(GraphLocation::std(dir.as_ref()))
    }
}

/// A path to a [`ProgramDescription`] file.
///
/// Can be created programmatically and automatically by running
/// [`SPDGGenCommand::run`] or you can create one manually if you can `cargo
/// dfpp` by hand with [`Self::custom`].
pub struct GraphLocation(PathBuf);

impl GraphLocation {
    /// Use the default graph file name in the specified directory.
    pub fn std(dir: impl AsRef<Path>) -> Self {
        Self(dir.as_ref().join(dfgraph::FLOW_GRAPH_OUT_NAME))
    }

    /// Use a completely custom path (directory and file name).
    pub fn custom(path: PathBuf) -> Self {
        Self(path)
    }

    /// Read and parse this graph file, returning a [`Context`] suitable for
    /// property enforcement.
    pub fn build_context(&self) -> Result<Arc<Context>> {
        simple_logger::init_with_env().unwrap();

        let desc = {
            let mut f = File::open(&self.0)?;
            serde_json::from_reader::<_, ProgramDescription>(&mut f)?
        };
        Ok(Arc::new(Context::new(desc)))
    }
}
