//! The query engine and framework for defining paralegal policies.
//!
//! It provides a state machine for programmatically extracting and parsing a
//! Semantic Program Dependence Graph (SPDG) and provides combinators and
//! queries on this graph for you to compose into policies.
//!
//! Next we show you the most common workflow, then explain the steps and show
//! you how to customize them to your needs.
//!
//! ```ignore
//! SPDGGenCommand::global()
//!     .run("project/dir/to/analyze")?
//!     .with_context(|ctx| my_property(ctx))
//! ```
//!
//! 1. [`SPDGGenCommand`] lets you programmatically invoke the SDPG extractor.
//!    The [`::global()`](SPDGGenCommand::global) method uses `cargo paralegal-flow` for
//!    this purpose, e.g. a global installation of `cargo-paralegal-flow` that was
//!    performed with `cargo install`.
//!
//!    - [`::custom()`](SPDGGenCommand::custom) lets you instead pick a
//!      different binary to run, for instance from a local installation.
//!    - [`.get_command()`](SPDGGenCommand::get_command) lets you customize the
//!      command, for instance by passing additional arguments such as `--debug`
//!      or `--dump`.
//! 2. [`.run(dir)`](SPDGGenCommand::run) invokes the extractor in `dir`,
//!    returning the path (as a [`GraphLocation`]) where the SPDG was written
//!    to.
//!
//!    Re-running this command often is cheap, because rustc skips the execution
//!    if there are no changes.
//!
//!    You may generate the graph manually and skip steps 1 and 2. In this case
//!    you can specify the [`GraphLocation`] with
//!    [`::std()`](GraphLocation::std), which uses the default graph file name
//!    or [`::custom()`](GraphLocation::custom) to use a custom file name.
//! 3. [`.with_context()`](GraphLocation::with_context) reads and parses the
//!    graph file, then invokes the provided closure with a [`Context`]. After
//!    the closure returns it automatically invokes
//!    [`Context::emit_diagnostics`].
//!
//! For information about how to specify policies see the [`Context`] struct.
//!
//! *Note:* This crate defines both the interface to the property checkers (via
//! [`Context`]) and the implementation of the engine (via
//! [`GraphLocation::build_context`]). A future version of this crate should
//! ideally separate those out so property checkers do not need to depend on the
//! checker implementation.

#![warn(missing_docs)]

use anyhow::{ensure, Result};
pub use paralegal_spdg;
use paralegal_spdg::ProgramDescription;
use std::{
    fs::File,
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
};

mod context;
mod flows_to;
#[macro_use]
pub mod diagnostics;
#[cfg(test)]
mod test_utils;

pub use self::{context::*, flows_to::CtrlFlowsTo};

/// Configuration of the `cargo paralegal-flow` command.
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
    /// Use a global installation of `paralegal-flow` via `cargo paralegal-flow`.
    pub fn global() -> Self {
        let mut cmd = Command::new("cargo");
        cmd.arg("paralegal-flow");
        Self::custom(cmd)
    }

    /// Use a custom binary or base invocation as command.
    pub fn custom(mut cmd: Command) -> Self {
        cmd.args(["--dump", "serialized-flow-graph"]);
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

/// A path to a [`ProgramDescription`] file from which a [`Context`] can be
/// created.
///
/// Can be created programmatically and automatically by running
/// [`SPDGGenCommand::run`] or you can create one manually if you can `cargo
/// paralegal-flow` by hand with [`Self::custom`].
pub struct GraphLocation(PathBuf);

impl GraphLocation {
    /// Use the default graph file name in the specified directory.
    pub fn std(dir: impl AsRef<Path>) -> Self {
        Self(dir.as_ref().join(paralegal_spdg::FLOW_GRAPH_OUT_NAME))
    }

    /// Use a completely custom path (directory and file name).
    pub fn custom(path: PathBuf) -> Self {
        Self(path)
    }

    /// Builds a context, then runs the property.
    ///
    /// Emits any recorded diagnostic messages to stdout and aborts the program
    /// if they were severe enough.
    pub fn with_context<A>(&self, prop: impl FnOnce(Arc<Context>) -> Result<A>) -> Result<A> {
        let ctx = Arc::new(self.build_context()?);
        let result = prop(ctx.clone())?;
        ctx.emit_diagnostics(std::io::stdout())?;
        Ok(result)
    }

    /// Read and parse this graph file, returning a [`Context`] suitable for
    /// property enforcement.
    ///
    /// Prefer using [`Self::with_context`] which takes care of emitting any
    /// diagnostic messages after the property is done.
    pub fn build_context(&self) -> Result<Context> {
        simple_logger::init_with_env().unwrap();

        let desc = {
            let mut f = File::open(&self.0)?;
            anyhow::Context::with_context(
                serde_json::from_reader::<_, ProgramDescription>(&mut f),
                || format!("Reading SPDG (JSON) from {}", self.0.display()),
            )?
        };
        Ok(Context::new(desc))
    }
}
