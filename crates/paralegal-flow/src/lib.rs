//! Ties together the crate and defines command line options.
//!
//! While this is technically a "library", it only is so for the purposes of
//! being able to reference the same code in the two executables `paralegal_flow` and
//! `cargo-paralegal-flow` (a structure suggested by [rustc_plugin]).
#![feature(rustc_private, min_specialization, box_patterns, let_chains)]
#[macro_use]
extern crate clap;
extern crate ordermap;
extern crate rustc_plugin;
extern crate rustc_utils;
extern crate serde;
extern crate toml;
#[macro_use]
extern crate lazy_static;
extern crate simple_logger;
#[macro_use]
extern crate log;
extern crate humantime;

extern crate petgraph;

extern crate num_derive;
extern crate num_traits;

extern crate rustc_abi;
extern crate rustc_arena;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_query_system;
extern crate rustc_serialize;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_type_ir;

extern crate either;

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::{fmt::Display, time::Instant};

use desc::ProgramDescription;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty;
use rustc_span::Symbol;
use ty::TyCtxt;

use rustc_driver::Compilation;
use rustc_plugin::CrateFilter;
use rustc_utils::mir::borrowck_facts;

use anyhow::{anyhow, Context as _, Result};
use either::Either;
// This import is sort of special because it comes from the private rustc
// dependencies and not from our `Cargo.toml`.

mod ana;
mod ann;
mod args;
mod discover;
mod stats;
//mod sah;
#[macro_use]
mod utils;
mod consts;
#[cfg(feature = "test")]
pub mod test_utils;

pub use paralegal_spdg as desc;

pub use crate::ann::db::MarkerCtx;

use ana::{MetadataLoader, SPDGGenerator};
use args::{AnalysisCtrl, Args, ClapArgs, Debugger, LogLevelConfig};
use consts::INTERMEDIATE_ARTIFACT_EXT;
use desc::utils::write_sep;
use stats::{Stats, TimedStat};
use utils::Print;

/// A struct so we can implement [`rustc_plugin::RustcPlugin`]
pub struct DfppPlugin;

/// Top level argument structure. This is only used for parsing. The actual
/// configuration of paralegal-flow [`struct@Args`] which is stored in `args`. `cargo_args` is
/// forwarded and `_progname` is only to comply with the calling convention of
/// `cargo` (it passes the program name as first argument).
#[derive(clap::Parser)]
#[clap(version = concat!(
    crate_version!(),
    "\nbuilt ", env!("BUILD_TIME"),
    "\ncommit ", env!("COMMIT_HASH"),
    "\nwith ", env!("RUSTC_VERSION"),
) , about)]
struct ArgWrapper {
    /// This argument doesn't do anything, but when cargo invokes `cargo-paralegal-flow`
    /// it always provides "paralegal-flow" as the first argument and since we parse with
    /// clap it otherwise complains about the superfluous argument.
    _progname: String,

    /// The actual arguments
    #[clap(flatten)]
    args: ClapArgs,
}

struct Callbacks {
    opts: &'static Args,
    stats: Stats,
    persist_metadata: bool,
}

/// Create the name of the file in which to store intermediate artifacts.
///
/// HACK(Justus): `TyCtxt::output_filenames` returns a file stem of
/// `lib<crate_name>-<hash>`, whereas `OutputFiles::with_extension` returns a file
/// stem of `<crate_name>-<hash>`. I haven't found a clean way to get the same
/// name in both places, so i just assume that these two will always have this
/// relation and prepend the `"lib"` here.
fn intermediate_out_file_path(tcx: TyCtxt) -> Result<PathBuf> {
    let rustc_out_file = tcx
        .output_filenames(())
        .with_extension(INTERMEDIATE_ARTIFACT_EXT);
    let dir = rustc_out_file
        .parent()
        .ok_or_else(|| anyhow!("{} has no parent", rustc_out_file.display()))?;
    let file = rustc_out_file
        .file_name()
        .ok_or_else(|| anyhow!("has no file name"))
        .and_then(|s| s.to_str().ok_or_else(|| anyhow!("not utf8")))
        .with_context(|| format!("{}", rustc_out_file.display()))?;

    let file = if file.starts_with("lib") {
        Cow::Borrowed(file)
    } else {
        format!("lib{file}").into()
    };

    Ok(dir.join(file.as_ref()))
}

impl Callbacks {
    fn in_context(&mut self, tcx: TyCtxt) -> Result<Compilation> {
        let compilation = if let Some(desc) = self.run_compilation(tcx)? {
            if self.opts.dbg().dump_spdg() {
                let out = std::fs::File::create("call-only-flow.gv").unwrap();
                paralegal_spdg::dot::dump(&desc, out).unwrap();
            }

            let ser = Instant::now();
            desc.canonical_write(self.opts.result_path()).unwrap();
            println!("Wrote graph to {}", self.opts.result_path().display());
            self.stats
                .record_timed(TimedStat::Serialization, ser.elapsed());

            println!("Analysis finished with timing: {}", self.stats);
            if self.opts.abort_after_analysis() {
                rustc_driver::Compilation::Stop
            } else {
                rustc_driver::Compilation::Continue
            }
        } else {
            println!("No compilation artifact");
            rustc_driver::Compilation::Continue
        };
        Ok(compilation)
    }

    fn run_compilation(&self, tcx: TyCtxt) -> Result<Option<ProgramDescription>> {
        tcx.sess.abort_if_errors();

        let loader = MetadataLoader::new(tcx);

        let (analysis_targets, mctx) = loader.clone().collect_and_emit_metadata(
            self.opts,
            self.persist_metadata
                .then(|| intermediate_out_file_path(tcx))
                .transpose()?,
        );
        tcx.sess.abort_if_errors();

        let mut gen = SPDGGenerator::new(mctx, self.opts, tcx, loader);

        (!analysis_targets.is_empty())
            .then(|| gen.analyze(analysis_targets))
            .transpose()
    }
}

struct NoopCallbacks {}

impl rustc_driver::Callbacks for NoopCallbacks {}

impl Callbacks {
    pub fn new(opts: &'static Args) -> Self {
        Self {
            opts,
            stats: Default::default(),
            persist_metadata: true,
        }
    }
}

impl rustc_driver::Callbacks for Callbacks {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        config.override_queries = Some(borrowck_facts::override_queries);
    }

    // This used to run `after_parsing` but that now makes `tcx.crates()` empty
    // (which interferes with external annotation resolution). So now it runs
    // `after_expansion` and so far that doesn't seem to break anything, but I'm
    // explaining this here in case that flowistry has some sort of issue with
    // that (when retrieving the MIR bodies for instance)
    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        queries
            .global_ctxt()
            .unwrap()
            .enter(|tcx| self.in_context(tcx))
            .unwrap()
    }
}

pub const CARGO_ENCODED_RUSTFLAGS: &str = "CARGO_ENCODED_RUSTFLAGS";

fn add_to_rustflags(new: impl IntoIterator<Item = String>) -> Result<(), std::env::VarError> {
    use std::env::{var, VarError};
    let mut prior = var(CARGO_ENCODED_RUSTFLAGS)
        .map(|flags| flags.split('\x1f').map(str::to_string).collect())
        .or_else(|err| {
            if matches!(err, VarError::NotPresent) {
                var("RUSTFLAGS").map(|flags| flags.split_whitespace().map(str::to_string).collect())
            } else {
                Err(err)
            }
        })
        .or_else(|err| {
            matches!(err, VarError::NotPresent)
                .then(Vec::new)
                .ok_or(err)
        })?;
    prior.extend(new);
    std::env::set_var(CARGO_ENCODED_RUSTFLAGS, prior.join("\x1f"));
    Ok(())
}

pub const PARALEGAL_RUSTC_FLAGS: [&str; 4] = [
    "--cfg",
    "paralegal",
    "-Zcrate-attr=feature(register_tool)",
    "-Zcrate-attr=register_tool(paralegal_flow)",
];

impl rustc_plugin::RustcPlugin for DfppPlugin {
    type Args = Args;

    fn version(&self) -> std::borrow::Cow<'static, str> {
        crate_version!().into()
    }

    fn driver_name(&self) -> std::borrow::Cow<'static, str> {
        "paralegal-flow".into()
    }

    fn args(
        &self,
        _target_dir: &rustc_plugin::Utf8Path,
    ) -> rustc_plugin::RustcPluginArgs<Self::Args> {
        use clap::Parser;
        let args = ArgWrapper::parse();

        // Override the SYSROOT so that it points to the version we were
        // compiled against.
        //
        // This is actually not necessary for *this* binary, but it will be
        // inherited by the calls to `cargo` and `rustc` done by `rustc_plugin`
        // and thus those will use the version of `std` that matches the nightly
        // compiler version we link against.
        std::env::set_var("SYSROOT", env!("SYSROOT_PATH"));

        add_to_rustflags(["--cfg".into(), "paralegal".into()]).unwrap();

        rustc_plugin::RustcPluginArgs {
            args: args.args.try_into().unwrap(),
            filter: CrateFilter::AllCrates,
        }
    }

    fn modify_cargo(&self, cargo: &mut std::process::Command, args: &Self::Args) {
        // All right so actually all that's happening here is that we drop the
        // "--all" that rustc_plugin automatically adds in such cases where the
        // arguments passed to paralegal indicate that we are supposed to run
        // only on select crates. Also we replace the `RUSTC_WORKSPACE_WRAPPER`
        // argument with `RUSTC_WRAPPER`
        // because of https://github.com/cognitive-engineering-lab/rustc_plugin/issues/19
        //
        // There isn't a nice way to do this so we hand-code what amounts to a
        // call to `cargo.clone()`, but with the one modification of removing
        // that argument.
        let args_select_package = args
            .cargo_args()
            .iter()
            .any(|a| a.starts_with("-p") || a == "--package");
        if args.target().is_some() | args_select_package {
            let mut new_cmd = std::process::Command::new(cargo.get_program());
            for (k, v) in cargo.get_envs() {
                if k == "RUSTC_WORKSPACE_WRAPPER" {
                    new_cmd.env("RUSTC_WRAPPER", v.unwrap());
                } else if let Some(v) = v {
                    new_cmd.env(k, v);
                } else {
                    new_cmd.env_remove(k);
                }
            }
            if let Some(wd) = cargo.get_current_dir() {
                new_cmd.current_dir(wd);
            }
            new_cmd.args(cargo.get_args().filter(|a| *a != "--all"));
            *cargo = new_cmd
        }
        if let Some(target) = args.target().as_ref() {
            if !args_select_package {
                cargo.args(["-p", target]);
            }
        }
        cargo.args(args.cargo_args());
    }

    fn run(
        self,
        mut compiler_args: Vec<String>,
        plugin_args: Self::Args,
    ) -> rustc_interface::interface::Result<()> {
        // return rustc_driver::RunCompiler::new(&compiler_args, &mut NoopCallbacks { }).run();
        // Setting the log levels is bit complicated because there are two level
        // filters going on in the logging crates. One is imposed by `log`
        // automatically and the other by `simple_logger` internally.

        // We use `log::set_max_level` later to selectively enable debug output
        // for specific targets. This max level is distinct from the one
        // provided to `with_level` below. Therefore in the case where we have a
        // `--debug` targeting a specific function we need to set the
        // `with_level` level lower and then increase it with
        // `log::set_max_level`.
        //println!("compiling {compiler_args:?}");

        let crate_name = compiler_args
            .iter()
            .enumerate()
            .find_map(|(i, s)| (s == "--crate-name").then_some(i))
            .and_then(|i| compiler_args.get(i + 1))
            .cloned();

        if let Some(dep_config) = crate_name
            .as_ref()
            .and_then(|s| plugin_args.build_config().dep.get(s))
        {
            compiler_args.extend(
                dep_config
                    .rust_features
                    .iter()
                    .map(|f| format!("-Zcrate-attr=feature({})", f)),
            );
        }

        let is_primary_package = std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();

        let our_target = plugin_args.target().map(|t| t.replace('-', "_"));

        let is_target = crate_name
            .as_ref()
            .and_then(|s| our_target.as_ref().map(|t| s == t))
            .unwrap_or(is_primary_package);

        let is_build_script = crate_name
            .as_ref()
            .map_or(false, |n| n == "build_script_build");

        debug!("Handling {}", crate_name.unwrap_or("".to_owned()));

        if !is_target || is_build_script {
            debug!("Is not target, skipping");
            return rustc_driver::RunCompiler::new(&compiler_args, &mut NoopCallbacks {}).run();
        }

        plugin_args.setup_logging();

        const RERUN_VAR: &str = "RERUN_WITH_PROFILER";
        if let Ok(debugger) = std::env::var(RERUN_VAR) {
            info!("Restarting with debugger '{debugger}'");
            let mut dsplit = debugger.split(' ');
            let mut cmd = std::process::Command::new(dsplit.next().unwrap());
            cmd.args(dsplit)
                .args(std::env::args())
                .env_remove(RERUN_VAR);
            std::process::exit(cmd.status().unwrap().code().unwrap_or(0));
        }

        let opts = Box::leak(Box::new(plugin_args));

        compiler_args.extend(PARALEGAL_RUSTC_FLAGS.iter().copied().map(ToOwned::to_owned));

        if let Some(dbg) = opts.attach_to_debugger() {
            dbg.attach()
        }

        debug!(
            "Arguments: {}",
            Print(|f| write_sep(f, " ", &compiler_args, Display::fmt))
        );
        rustc_driver::RunCompiler::new(&compiler_args, &mut Callbacks::new(opts)).run()
    }
}

impl Debugger {
    fn attach(self) {
        use std::process::{id, Command};
        use std::thread::sleep;
        use std::time::Duration;

        match self {
            Debugger::CodeLldb => {
                let url = format!(
                    "vscode://vadimcn.vscode-lldb/launch/config?{{'request':'attach','pid':{}}}",
                    id()
                );
                Command::new("code")
                    .arg("--open-url")
                    .arg(url)
                    .output()
                    .unwrap();
                sleep(Duration::from_millis(1000));
            }
        }
    }
}
