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
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_parse;
extern crate rustc_query_system;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_type_ir;

use ann::dump_markers;
use args::{ClapArgs, Debugger, LogLevelConfig};
use desc::utils::write_sep;

use flowistry_pdg_construction::body_cache::{dump_mir_and_borrowck_facts, intermediate_out_dir};
use log::Level;
use paralegal_spdg::{AnalyzerStats, STAT_FILE_EXT};
use rustc_middle::ty::TyCtxt;
use rustc_plugin::CrateFilter;

pub use std::collections::{HashMap, HashSet};
use std::{
    fmt::Display,
    fs::File,
    io::BufWriter,
    path::PathBuf,
    time::{Duration, Instant},
};

// This import is sort of special because it comes from the private rustc
// dependencies and not from our `Cargo.toml`.
pub extern crate either;
pub use either::Either;

pub use rustc_span::Symbol;

pub mod ana;
pub mod ann;
mod args;
pub mod dbg;
mod discover;
mod stats;
#[macro_use]
pub mod utils;
#[cfg(feature = "test")]
pub mod test_utils;

pub use paralegal_spdg as desc;

pub use crate::ann::db::MarkerCtx;
pub use args::{AnalysisCtrl, Args, BuildConfig, DepConfig, DumpArgs, MarkerControl};

use crate::{
    stats::{Stats, TimedStat},
    utils::Print,
};

pub const EXTRA_RUSTC_ARGS: &[&str] = &[
    "--cfg",
    "paralegal",
    "-Zcrate-attr=feature(register_tool)",
    "-Zcrate-attr=register_tool(paralegal_flow)",
];

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

struct Callbacks<'a> {
    opts: &'static Args,
    stats: Stats,
    rustc_second_timer: Option<Instant>,
    stat_ref: &'a mut Option<AnalyzerStats>,
    output_location: &'a mut Option<PathBuf>,
    time: &'a mut DumpStats,
}

struct NoopCallbacks;

impl rustc_driver::Callbacks for NoopCallbacks {}

impl<'a> Callbacks<'a> {
    pub fn new(
        opts: &'static Args,
        stat_ref: &'a mut Option<AnalyzerStats>,
        output_location: &'a mut Option<PathBuf>,
        time: &'a mut DumpStats,
    ) -> Self {
        Self {
            opts,
            stats: Default::default(),
            rustc_second_timer: None,
            stat_ref,
            output_location,
            time,
        }
    }
}

#[derive(serde::Deserialize, serde::Serialize)]
struct DumpStats {
    dump_time: Duration,
    total_time: Duration,
    tycheck_time: Duration,
}

impl DumpStats {
    fn zero() -> Self {
        Self {
            dump_time: Duration::ZERO,
            total_time: Duration::ZERO,
            tycheck_time: Duration::ZERO,
        }
    }

    fn add(&self, other: &Self) -> Self {
        Self {
            total_time: self.total_time + other.total_time,
            dump_time: self.dump_time + other.dump_time,
            tycheck_time: self.tycheck_time + other.tycheck_time,
        }
    }
}

struct DumpOnlyCallbacks<'a> {
    time: &'a mut DumpStats,
    output_location: &'a mut Option<PathBuf>,
}

const INTERMEDIATE_STAT_EXT: &str = "stats.json";

fn dump_mir_and_update_stats(tcx: TyCtxt, timer: &mut DumpStats) {
    let (tycheck_time, dump_time) = dump_mir_and_borrowck_facts(tcx);
    let dump_marker_start = Instant::now();
    dump_markers(tcx);
    timer.dump_time = dump_marker_start.elapsed() + dump_time;
    timer.tycheck_time = tycheck_time;
}

impl rustc_driver::Callbacks for DumpOnlyCallbacks<'_> {
    fn after_expansion(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'_>,
    ) -> rustc_driver::Compilation {
        dump_mir_and_update_stats(tcx, self.time);
        assert!(self
            .output_location
            .replace(intermediate_out_dir(tcx, INTERMEDIATE_STAT_EXT))
            .is_none());
        rustc_driver::Compilation::Continue
    }
}

impl rustc_driver::Callbacks for Callbacks<'_> {
    fn after_expansion(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'_>,
    ) -> rustc_driver::Compilation {
        self.stats
            .record_timed(TimedStat::Rustc, self.stats.elapsed());
        let compilation = self.run_the_analyzer(tcx);
        self.rustc_second_timer = Some(Instant::now());
        compilation
    }

    // This used to run `after_parsing` but that now makes `tcx.crates()` empty
    // (which interferes with external annotation resolution). So now it runs
    // `after_expansion` and so far that doesn't seem to break anything, but I'm
    // explaining this here in case that flowistry has some sort of issue with
    // that (when retrieving the MIR bodies for instance)
    fn after_analysis(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        _tcx: TyCtxt<'_>,
    ) -> rustc_driver::Compilation {
        self.stats
            .record_timed(TimedStat::Rustc, self.rustc_second_timer.unwrap().elapsed());
        rustc_driver::Compilation::Continue
    }
}

impl Callbacks<'_> {
    fn run_the_analyzer(&mut self, tcx: TyCtxt<'_>) -> rustc_driver::Compilation {
        dump_markers(tcx);
        tcx.dcx().abort_if_errors();
        let (desc, mut stats) =
            discover::CollectingVisitor::new(tcx, self.opts, self.stats.clone())
                .run()
                .unwrap();
        info!("All elems walked");
        tcx.dcx().abort_if_errors();

        if self.opts.dbg().dump_spdg() {
            let out = std::fs::File::create("call-only-flow.gv").unwrap();
            paralegal_spdg::dot::dump(&desc, out).unwrap();
        }

        self.stats.measure(TimedStat::Serialization, || {
            desc.canonical_write(self.opts.result_path()).unwrap()
        });

        stats.serialization_time = self.stats.get_timed(TimedStat::Serialization);

        println!("Analysis finished with timing: {}", self.stats);

        assert!(self.stat_ref.replace(stats).is_none());

        assert!(self
            .output_location
            .replace(intermediate_out_dir(tcx, INTERMEDIATE_STAT_EXT))
            .is_none());

        if self.opts.abort_after_analysis() {
            rustc_driver::Compilation::Stop
        } else {
            self.stats.measure(TimedStat::MirEmission, || {
                dump_mir_and_update_stats(tcx, self.time);
            });
            rustc_driver::Compilation::Continue
        }
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

#[derive(strum::AsRefStr, PartialEq, Eq)]
enum CrateHandling {
    JustCompile,
    CompileAndDump,
    Analyze,
}

struct CrateInfo {
    name: Option<String>,
    handling: CrateHandling,
    #[allow(dead_code)]
    is_build_script: bool,
}

impl CrateInfo {
    pub fn name_or_default(&self) -> &str {
        self.name.as_deref().unwrap_or("unnamed")
    }
}

/// Also adds and additional features required by the Paralegal build config
fn how_to_handle_this_crate(plugin_args: &Args, compiler_args: &mut Vec<String>) -> CrateInfo {
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

    let is_build_script = matches!(
        &crate_name,
        Some(krate) if krate == "build_script_build"
    );
    let handling = match &crate_name {
        _ if is_build_script => CrateHandling::JustCompile,
        Some(krate)
            if matches!(
                plugin_args
                    .target(),
                    Some(target) if &target.replace('-', "_") == krate
            ) =>
        {
            CrateHandling::Analyze
        }
        _ if std::env::var("CARGO_PRIMARY_PACKAGE").is_ok() => CrateHandling::Analyze,
        Some(krate) if plugin_args.anactrl().included().contains(krate) => {
            CrateHandling::CompileAndDump
        }
        _ => CrateHandling::JustCompile,
    };

    CrateInfo {
        name: crate_name,
        handling,
        is_build_script,
    }
}

impl rustc_plugin::RustcPlugin for DfppPlugin {
    type Args = Args;

    fn version(&self) -> std::borrow::Cow<'static, str> {
        crate_version!().into()
    }

    fn driver_name(&self) -> std::borrow::Cow<'static, str> {
        "paralegal-flow".into()
    }

    fn reported_driver_version(&self) -> std::borrow::Cow<'static, str> {
        env!("RUSTC_VERSION").into()
    }

    fn hash_config(&self, args: &Self::Args, hasher: &mut impl std::hash::Hasher) {
        args.hash_config(hasher);
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

        let mut output_path_location = None;
        let mut dump_stats = DumpStats::zero();
        let start = Instant::now();
        let mut stat_ref = None;
        let out_path = plugin_args.result_path().to_owned();

        let info = how_to_handle_this_crate(&plugin_args, &mut compiler_args);
        debug!(
            "Handling crate {} as {}",
            info.name_or_default(),
            info.handling.as_ref()
        );
        {
            let mut callbacks = match info.handling {
                CrateHandling::JustCompile => {
                    Box::new(NoopCallbacks) as Box<dyn rustc_driver::Callbacks + Send>
                }
                CrateHandling::CompileAndDump => {
                    compiler_args.extend(EXTRA_RUSTC_ARGS.iter().copied().map(ToString::to_string));
                    Box::new(DumpOnlyCallbacks {
                        time: &mut dump_stats,
                        output_location: &mut output_path_location,
                    })
                }
                CrateHandling::Analyze => {
                    plugin_args.setup_logging();

                    let opts = Box::leak(Box::new(plugin_args));

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

                    compiler_args.extend(EXTRA_RUSTC_ARGS.iter().copied().map(ToString::to_string));
                    if opts.verbosity() >= Level::Debug {
                        compiler_args.push("-Ztrack-diagnostics".to_string());
                    }

                    if let Some(dbg) = opts.attach_to_debugger() {
                        dbg.attach()
                    }

                    debug!(
                        "Arguments: {}",
                        Print(|f| write_sep(f, " ", &compiler_args, Display::fmt))
                    );
                    Box::new(Callbacks::new(
                        opts,
                        &mut stat_ref,
                        &mut output_path_location,
                        &mut dump_stats,
                    ))
                }
            };

            rustc_driver::RunCompiler::new(&compiler_args, callbacks.as_mut()).run();
        };
        if info.handling != CrateHandling::JustCompile {
            let filepath = output_path_location
                .take()
                .expect("Output path should be set");
            dump_stats.total_time = start.elapsed();
            println!(
                "Writing statistics for dependency to {}",
                filepath.display()
            );
            let out = BufWriter::new(File::create(filepath).unwrap());
            serde_json::to_writer(out, &dump_stats).unwrap();
        }
        if info.handling == CrateHandling::Analyze {
            let out = BufWriter::new(File::create(out_path.with_extension(STAT_FILE_EXT)).unwrap());
            let mut stat = stat_ref.take().expect("stats must have been set");
            let self_time = start.elapsed();
            // See ana/mod.rs for explanations as to these adjustments.
            stat.self_time = self_time;
            serde_json::to_writer(out, &stat).unwrap();
        }
        debug!("Finished with crate {}", info.name_or_default());
        Ok(())
    }
}

impl Debugger {
    fn attach(self) {
        use std::process::{id, Command};
        use std::thread::sleep;

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
