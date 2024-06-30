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

extern crate core;

use anyhow::{ensure, Result};
pub use paralegal_spdg;
use paralegal_spdg::utils::TruncatedHumanTime;
pub use paralegal_spdg::{
    traverse::EdgeSelection, GlobalNode, IntoIterGlobalNodes, ProgramDescription,
};
use std::time::{Duration, Instant};
use std::{
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
};

pub mod algo;
mod context;
#[macro_use]
pub mod diagnostics;
#[cfg(test)]
mod test_utils;

pub use self::{
    algo::flows_to::CtrlFlowsTo,
    algo::flows_to::DataAndControlInfluencees,
    context::*,
    diagnostics::{CombinatorContext, Diagnostics, PolicyContext},
};

#[derive(Clone, Debug)]
/// Statistics about the runtime of the various parts of a policy.
pub struct Stats {
    /// Runtime of the `paralegal-flow` command
    pub analysis: Option<Duration>,
    /// How long it took to create the indices
    pub context_contruction: Duration,
    /// How long the policy runs
    pub policy: Duration,
    /// How long it took to read in the graph description
    pub deserialization: Duration,
}

impl std::fmt::Display for Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Analysis: ")?;
        if let Some(ana) = self.analysis {
            TruncatedHumanTime::from(ana).fmt(f)?;
        } else {
            f.write_str("no measurement")?;
        }
        write!(
            f,
            ", Index Creation: {}, Policy Execution: {}, Deser: {}",
            TruncatedHumanTime::from(self.context_contruction),
            TruncatedHumanTime::from(self.policy),
            TruncatedHumanTime::from(self.deserialization),
        )
    }
}

/// Result of running a policy
pub struct PolicyReturn<A> {
    /// If the policy wants to return additional data, this is it
    pub result: A,
    /// Did the policy succeed.
    pub success: bool,
    /// Runtime statistics
    pub stats: Stats,
}

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
    pub fn custom(cmd: Command) -> Self {
        Self(cmd)
    }

    /// Mutably borrow the command to perform further customization.
    ///
    /// This gives you raw access to the underlying command. Be aware that if
    /// you pass `--` with [`Command::arg`] or [`Command::args`] then methods
    /// such as [`Self::external_annotations`] and
    /// [`Self::abort_after_analysis`] not longer work properly after this call.
    pub fn get_command(&mut self) -> &mut Command {
        &mut self.0
    }

    /// Pass the provided file as `--external-annotations` to the command.
    pub fn external_annotations(&mut self, file: impl AsRef<Path>) -> &mut Self {
        self.0
            .args(["--external-annotations".as_ref(), file.as_ref().as_os_str()]);
        self
    }

    /// Abort compilation once the analysis artifacts have been created. Also
    /// sets the expectation for the compilation to succeed to `false`.
    pub fn abort_after_analysis(&mut self) -> &mut Self {
        self.0.arg("--abort-after-analysis");
        self
    }

    /// Consume the created command and execute it in the specified directory.
    ///
    /// Errors if executing the underlying [`Command`] fails or if it does not
    /// terminate successfully.
    ///
    /// To run yor properties on the results see [`GraphLocation`].
    pub fn run(&mut self, dir: impl AsRef<Path>) -> Result<GraphLocation> {
        let start = Instant::now();
        let status = self.0.current_dir(dir.as_ref()).status()?;
        ensure!(status.success(), "Compilation failed");
        let mut loc = GraphLocation::std(dir.as_ref());
        loc.construction_time = Some(start.elapsed());
        Ok(loc)
    }
}

/// A path to a [`ProgramDescription`] file from which a [`Context`] can be
/// created.
///
/// Can be created programmatically and automatically by running
/// [`SPDGGenCommand::run`] or you can create one manually if you can `cargo
/// paralegal-flow` by hand with [`Self::custom`].
pub struct GraphLocation {
    path: PathBuf,
    construction_time: Option<Duration>,
}

impl GraphLocation {
    /// Use the default graph file name in the specified directory.
    pub fn std(dir: impl AsRef<Path>) -> Self {
        Self {
            path: dir.as_ref().join(paralegal_spdg::FLOW_GRAPH_OUT_NAME),
            construction_time: None,
        }
    }

    /// Use a completely custom path (directory and file name).
    pub fn custom(path: PathBuf) -> Self {
        Self {
            path,
            construction_time: None,
        }
    }

    /// Inspect the path that will be loaded
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Builds a context, then runs the property.
    ///
    /// Emits any recorded diagnostic messages to stdout and aborts the program
    /// if they were severe enough.
    pub fn with_context<A>(
        &self,
        prop: impl FnOnce(Arc<Context>) -> Result<A>,
    ) -> Result<PolicyReturn<A>> {
        self.with_context_configured(Default::default(), prop)
    }

    /// Builds a context, then runs the property.
    ///
    /// Emits any recorded diagnostic messages to stdout and aborts the program
    /// if they were severe enough.
    pub fn with_context_configured<A>(
        &self,
        config: Config,
        prop: impl FnOnce(Arc<Context>) -> Result<A>,
    ) -> Result<PolicyReturn<A>> {
        let ctx = Arc::new(self.build_context(config)?);
        assert_warning!(
            ctx,
            !ctx.desc().controllers.is_empty(),
            "No controllers found. Your policy is likely to be vacuous."
        );
        let start = Instant::now();
        let result = prop(ctx.clone())?;

        let success = ctx.emit_diagnostics()?;
        Ok(PolicyReturn {
            success,
            result,
            stats: Stats {
                analysis: ctx.stats.pdg_construction,
                context_contruction: ctx.stats.precomputation,
                deserialization: ctx.stats.deserialization.unwrap(),
                policy: start.elapsed(),
            },
        })
    }

    /// Read and parse this graph file, returning a [`Context`] suitable for
    /// property enforcement.
    ///
    /// Prefer using [`Self::with_context`] which takes care of emitting any
    /// diagnostic messages after the property is done.
    pub fn build_context(&self, config: Config) -> Result<Context> {
        let _ = simple_logger::init_with_env();

        let deser_started = Instant::now();
        let desc = ProgramDescription::canonical_read(&self.path)?;
        let mut ctx = Context::new(desc, config);
        ctx.stats.pdg_construction = self.construction_time;
        ctx.stats.deserialization = Some(deser_started.elapsed());
        Ok(ctx)
    }
}

/// Configuration for the framework
#[derive(Clone, Debug)]
pub struct Config {
    /// How much information to retain for error messages in `always_happens_before`
    pub always_happens_before_tracing: algo::ahb::TraceLevel,
    /// Whether tho precompute an index for `flows_to` queries with
    /// `EdgeSelection::Data` or whether to use a new DFS every time.
    pub use_flows_to_index: bool,
    /// Where to write output to
    pub get_output_writer: fn() -> Box<dyn std::io::Write>,
}

fn default_output() -> Box<dyn std::io::Write> {
    Box::new(std::io::stdout())
}

impl Default for Config {
    fn default() -> Self {
        Config {
            always_happens_before_tracing: algo::ahb::TraceLevel::StartAndEnd,
            use_flows_to_index: false,
            get_output_writer: default_output,
        }
    }
}

/// A convenience macro that uses `file!`, `line!` and `column!` to return the
/// string `"file:line:column"`. This can be used to mention policy source
/// locations in policies.
///
/// If additional arguments are procided these are `concat!`ed to the end with a
/// space in betwee the location and the rest.
#[macro_export]
macro_rules! loc {
    () => {
        concat!(file!(), ':', line!(), ':', column!(),)
    };
    ($($t:tt)+) => {
        concat!(file!(), ':', line!(), ':', column!(), ' ', $($t)+)
    };
}
