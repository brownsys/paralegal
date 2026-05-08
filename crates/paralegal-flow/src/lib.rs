//! Ties together the crate and defines command line options.
//!
//! While this is technically a "library", it only is so for the purposes of
//! being able to reference the same code in the two executables `paralegal_flow` and
//! `cargo-paralegal-flow` (a structure suggested by [rustc_plugin]).
#![feature(rustc_private, min_specialization)]
#![recursion_limit = "256"]

extern crate rustc_abi;
extern crate rustc_arena;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_driver_impl;
extern crate rustc_error_messages;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_lint_defs;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_parse;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_stable_hash;
extern crate rustc_target;
extern crate rustc_type_ir;

use flowistry_pdg_construction::source_access::{
    dump_mir_and_borrowck_facts, intermediate_out_dir, mir_borrowck,
};
use paralegal_spdg::{AnalyzerStats, FLOW_GRAPH_EXT, ProgramDescription, STAT_FILE_EXT};

use rustc_interface::Config;
use rustc_middle::ty::TyCtxt;
use rustc_span::ErrorGuaranteed;
use tracing::{debug, error, info};

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
mod ctx;
pub mod dbg;
mod discover;
mod stats;
#[macro_use]
pub mod utils;
#[cfg(feature = "test")]
pub mod test_utils;

pub use paralegal_spdg as desc;

pub use crate::ann::db::MarkerCtx;
use crate::{
    stats::{Stats, TimedStat},
    utils::Print,
};
use ann::dump_markers;
pub use args::{AnalysisCtrl, Args, BuildConfig, DepConfig, DumpArgs};
use cargo_paralegal_flow::{ClapArgs, Debugger};
pub use ctx::Pctx;
use desc::utils::write_sep;

pub const EXTRA_RUSTC_ARGS: &[&str] = &[
    "--cfg",
    "paralegal",
    "-Zcrate-attr=feature(register_tool)",
    "-Zcrate-attr=register_tool(paralegal_flow)",
];

/// Top level argument structure. This is only used for parsing. The actual
/// configuration of paralegal-flow [`struct@Args`] which is stored in `args`. `cargo_args` is
/// forwarded and `_progname` is only to comply with the calling convention of
/// `cargo` (it passes the program name as first argument).
#[derive(clap::Parser)]
#[clap(version = concat!(
    clap::crate_version!(),
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

trait FinalizingCallbacks: rustc_driver::Callbacks + Send {
    fn upcast_mut(&mut self) -> &mut (dyn rustc_driver::Callbacks + Send);

    fn finalize(&mut self) {}
}

struct Callbacks {
    opts: &'static Args,
    stats: Stats,
    rustc_second_timer: Option<Instant>,
    stat_ref: Option<AnalyzerStats>,
    start: Instant,
    dump_stats: DumpStats,
    output_location: Option<PathBuf>,
}

struct NoopCallbacks;

impl rustc_driver::Callbacks for NoopCallbacks {}

impl FinalizingCallbacks for NoopCallbacks {
    fn upcast_mut(&mut self) -> &mut (dyn rustc_driver::Callbacks + Send) {
        self
    }
}

impl Callbacks {
    pub fn new(opts: &'static Args) -> Self {
        Self {
            opts,
            stats: Default::default(),
            rustc_second_timer: None,
            stat_ref: None,
            start: Instant::now(),
            dump_stats: DumpStats::zero(),
            output_location: None,
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

struct DumpOnlyCallbacks {
    time: DumpStats,
    start: Instant,
    output_location: Option<PathBuf>,
}

impl DumpOnlyCallbacks {
    fn new() -> Self {
        Self {
            time: DumpStats::zero(),
            start: Instant::now(),
            output_location: None,
        }
    }
}

const INTERMEDIATE_STAT_EXT: &str = "stats.json";

fn dump_mir_and_update_stats(tcx: TyCtxt, timer: &mut DumpStats) {
    let (tycheck_time, dump_time) = dump_mir_and_borrowck_facts(tcx);
    let dump_marker_start = Instant::now();
    dump_markers(tcx);
    timer.dump_time = dump_marker_start.elapsed() + dump_time;
    timer.tycheck_time = tycheck_time;
}

fn configure(config: &mut Config) {
    config.override_queries = Some(|_, providers| providers.queries.mir_borrowck = mir_borrowck);
    assert_eq!(config.opts.unstable_opts.threads, 1);
    //config.opts.unstable_opts.polonius = Polonius::Next;
    // We don't care about emitting any lints. Users can get those when they
    // compile normally.  This could be added back if needed, but on toolchain
    // 2026-04-20 we need to at least disable `tail_expr_drop_order` or we get
    // issues with borrowcheck fact generation.
    config.opts.lint_cap = Some(rustc_lint_defs::Allow);
    // TODO add crate attr and cfg paralegal
}

impl rustc_driver::Callbacks for DumpOnlyCallbacks {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        configure(config)
    }

    fn after_expansion(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'_>,
    ) -> rustc_driver::Compilation {
        dump_mir_and_update_stats(tcx, &mut self.time);
        self.output_location = Some(intermediate_out_dir(tcx, INTERMEDIATE_STAT_EXT));
        rustc_driver::Compilation::Continue
    }
}

impl FinalizingCallbacks for DumpOnlyCallbacks {
    fn upcast_mut(&mut self) -> &mut (dyn rustc_driver::Callbacks + Send) {
        self
    }

    fn finalize(&mut self) {
        let filepath = self
            .output_location
            .as_ref()
            .expect("Output path should be set");
        self.time.total_time = self.start.elapsed();
        let out = BufWriter::new(File::create(filepath).unwrap());
        serde_json::to_writer(out, &self.time).unwrap();
    }
}

impl rustc_driver::Callbacks for Callbacks {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        configure(config)
    }

    fn after_expansion<'tcx>(
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

impl FinalizingCallbacks for Callbacks {
    fn upcast_mut(&mut self) -> &mut (dyn rustc_driver::Callbacks + Send) {
        self
    }

    fn finalize(&mut self) {
        let out_path = self.opts.result_path().to_owned();
        let out = BufWriter::new(File::create(out_path.with_extension(STAT_FILE_EXT)).unwrap());
        let stat = self.stat_ref.as_mut().expect("stats must have been set");
        let self_time = self.start.elapsed();
        // See ana/mod.rs for explanantions as to these adjustments.
        stat.self_time = self_time;
        serde_json::to_writer(out, &stat).unwrap();

        let filepath = self
            .output_location
            .as_ref()
            .expect("Output path should be set");
        self.dump_stats.total_time = self.start.elapsed();
        let out = BufWriter::new(File::create(filepath).unwrap());
        serde_json::to_writer(out, &self.dump_stats).unwrap();
    }
}

impl Callbacks {
    pub fn run_in_context_without_writing_stats(
        &mut self,
        tcx: TyCtxt<'_>,
    ) -> anyhow::Result<(ProgramDescription, AnalyzerStats)> {
        let dump_marker_start = Instant::now();
        dump_markers(tcx);
        self.dump_stats.dump_time += dump_marker_start.elapsed();
        tcx.dcx().abort_if_errors();
        let vis = discover::CollectingVisitor::new(tcx, self.opts, self.stats.clone());
        let mut generator = vis.run();
        let (desc, stats) = generator.analyze()?;
        info!(num_controllers = desc.controllers.len(), "All elems walked");
        tcx.dcx().abort_if_errors();

        if self.opts.dbg().dump_spdg() {
            let td = std::env::var("CARGO_MANIFEST_DIR").unwrap_or(".".to_string());
            let mut pb = std::path::PathBuf::from(&td);
            pb.push("target");
            if !pb.exists() {
                error!(
                    "Target directory {} should exist, will create one.",
                    pb.display()
                );
            }
            pb.push("paralegal-dump");
            pb.push("graph");
            std::fs::create_dir_all(&pb).unwrap();
            paralegal_spdg::dot::dump_all_separate(&desc, |name| {
                let mut pb = pb.clone();
                pb.push(format!(
                    "{}",
                    Print(|f| write_sep(f, "-", name.iter(), Display::fmt))
                ));
                pb.set_extension("graph.gv");
                pb
            })?;
        }

        generator
            .marker_ctx()
            .dump_marker_stats(std::fs::File::create(
                self.opts.result_path().with_extension("marker_stats.json"),
            )?);
        Ok((desc, stats))
    }

    fn run_the_analyzer(&mut self, tcx: TyCtxt<'_>) -> rustc_driver::Compilation {
        let abort = (|| {
            assert!(
                self.output_location
                    .replace(intermediate_out_dir(tcx, INTERMEDIATE_STAT_EXT))
                    .is_none()
            );
            let (desc, mut stats) = self.run_in_context_without_writing_stats(tcx)?;
            self.stats.measure(TimedStat::Serialization, || {
                desc.canonical_write(self.opts.result_path()).unwrap()
            });

            stats.serialization_time = self.stats.get_timed(TimedStat::Serialization);

            self.stats.measure(TimedStat::Serialization, || {
                desc.canonical_write(tcx.output_filenames(()).with_extension(FLOW_GRAPH_EXT))
                    .unwrap()
            });

            assert!(self.stat_ref.replace(stats).is_none());
            anyhow::Ok(self.opts.abort_after_analysis())
        })()
        .unwrap();

        if abort {
            rustc_driver::Compilation::Stop
        } else {
            self.stats.measure(TimedStat::MirEmission, || {
                dump_mir_and_update_stats(tcx, &mut self.dump_stats);
            });
            rustc_driver::Compilation::Continue
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum CrateHandling {
    JustCompile,
    CompileAndDump,
    Analyze,
}

#[derive(Debug)]
struct CrateInfo {
    #[allow(dead_code)]
    name: Option<String>,
    handling: CrateHandling,
    #[allow(dead_code)]
    is_build_script: bool,
}

impl CrateInfo {
    #[allow(dead_code)]
    pub fn name_or_default(&self) -> &str {
        self.name.as_deref().unwrap_or("unnamed")
    }
}

/// Also adds and additional features required by the Paralegal build config
fn how_to_handle_this_crate(plugin_args: &Args, compiler_args: &mut Vec<String>) -> CrateInfo {
    // TODO do this configuration in `config`
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
    let mut info = CrateInfo {
        name: crate_name.clone(),
        handling: CrateHandling::JustCompile,
        is_build_script,
    };
    if is_build_script
        || compiler_args
            .iter()
            .any(|a| a == "--print" || a.starts_with("--print="))
    {
        return info;
    }
    let name = info
        .name
        .as_ref()
        .expect("crate name should be known at this point");
    if plugin_args.anactrl().included(name) {
        info.handling = CrateHandling::CompileAndDump;
    }
    if let Some(target) = plugin_args.target() {
        if target == name {
            info.handling = CrateHandling::Analyze;
        }
    } else if std::env::var("CARGO_PRIMARY_PACKAGE").is_ok() {
        info.handling = CrateHandling::Analyze;
    }
    info
}

pub fn run(mut compiler_args: Vec<String>, plugin_args: Args) -> Result<(), ErrorGuaranteed> {
    let handling = how_to_handle_this_crate(&plugin_args, &mut compiler_args);
    debug!(?handling, "Crate handling");
    compiler_args.extend(EXTRA_RUSTC_ARGS.iter().copied().map(ToString::to_string));
    let mut callbacks = match handling.handling {
        CrateHandling::JustCompile => Box::new(NoopCallbacks) as Box<dyn FinalizingCallbacks>,
        CrateHandling::CompileAndDump => Box::new(DumpOnlyCallbacks::new()),
        CrateHandling::Analyze => {
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

            if cfg!(debug_assertions) {
                compiler_args.push("-Ztrack-diagnostics".to_string());
            }

            if let Some(dbg) = opts.attach_to_debugger() {
                attach_debugger(dbg)
            }

            Box::new(Callbacks::new(opts))
        }
    };

    let upcasted_callback = callbacks.upcast_mut();

    rustc_driver_impl::run_compiler(&compiler_args, upcasted_callback);

    callbacks.finalize();
    Ok(())
}

fn attach_debugger(debugger: Debugger) {
    use std::process::{Command, id};
    use std::thread::sleep;

    match debugger {
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
