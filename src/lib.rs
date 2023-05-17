//! Ties together the crate and defines command line options.
//!
//! While this is technically a "library", it only is so for the purposes of
//! being able to reference the same code in the two executables `dfpp` and
//! `cargo-dfpp` (a structure suggested by [rustc_plugin]).
#![feature(rustc_private)]
#![feature(min_specialization)]
#![feature(drain_filter)]
#![feature(box_patterns)]
#[macro_use]
extern crate clap;
extern crate ordermap;
extern crate rustc_plugin;
extern crate serde;
extern crate toml;
#[macro_use]
extern crate lazy_static;
extern crate simple_logger;
#[macro_use]
extern crate log;
extern crate humantime;

extern crate petgraph;

#[macro_use]
pub extern crate rustc_index;
extern crate rustc_serialize;

pub mod rust {
    //! Exposes the rustc external crates (this mod is just to tidy things up).
    pub extern crate rustc_arena;
    pub extern crate rustc_ast;
    pub extern crate rustc_borrowck;
    pub extern crate rustc_data_structures;
    pub extern crate rustc_driver;
    pub extern crate rustc_hir;
    pub extern crate rustc_interface;
    pub extern crate rustc_middle;
    pub extern crate rustc_mir_dataflow;
    pub extern crate rustc_query_system;
    pub extern crate rustc_serialize;
    pub extern crate rustc_span;
    pub use super::rustc_index;

    pub use rustc_ast as ast;
    pub use rustc_hir as hir;
    pub use rustc_middle::mir;
    pub use rustc_middle::ty;

    pub use rustc_middle::dep_graph::DepGraph;
    pub use ty::TyCtxt;

    pub use hir::def_id::{DefId, LocalDefId};
    pub use mir::Location;
}

use args::LogLevelConfig;
use pretty::DocBuilder;
use rust::*;

use flowistry::mir::borrowck_facts;
pub use std::collections::{HashMap, HashSet};

// This import is sort of special because it comes from the private rustc
// dependencies and not from our `Cargo.toml`.
pub extern crate either;
pub use either::Either;

pub use rustc_span::Symbol;

pub mod ana;
pub mod ann_parse;
mod args;
pub mod dbg;
pub mod desc;
mod discover;
pub mod frg;
pub mod ir;
mod sah;
pub mod serializers;
#[macro_use]
pub mod utils;
pub mod consts;

pub use args::{AnalysisCtrl, Args, DbgArgs, ModelCtrl};

use crate::utils::outfile_pls;

/// A struct so we can implement [`rustc_plugin::RustcPlugin`]
pub struct DfppPlugin;

/// Top level argument structure. This is only used for parsing. The actual
/// configuration of dfpp [`struct@Args`] which is stored in `args`. `cargo_args` is
/// forwarded and `_progname` is only to comply with the calling convention of
/// `cargo` (it passes the program name as first argument).
#[derive(clap::Parser)]
#[clap(version = concat!(crate_version!(), "\nbuilt ", env!("BUILD_TIME"), "\ncommit ", env!("COMMIT_HASH")), about)]
struct ArgWrapper {
    /// This argument doesn't do anything, but when cargo invokes `cargo-dfpp`
    /// it always provides "dfpp" as the first argument and since we parse with
    /// clap it otherwise complains about the superfluous argument.
    _progname: String,

    /// The actual arguments
    #[clap(flatten)]
    args: Args,

    /// Pass through for additional cargo arguments (like --features)
    #[clap(last = true)]
    cargo_args: Vec<String>,
}

struct Callbacks {
    opts: &'static Args,
}

struct NoopCallbacks {}

impl rustc_driver::Callbacks for NoopCallbacks {}

type RawExternalMarkers = HashMap<String, Vec<desc::MarkerAnnotation>>;

#[derive(serde::Deserialize, serde::Serialize)]
pub struct AdditionalInfo {
    #[serde(with = "crate::serializers::serde_map_via_vec")]
    pub call_sites: HashMap<String, desc::CallSite>,
}

impl rustc_driver::Callbacks for Callbacks {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        config.override_queries = Some(borrowck_facts::override_queries);
    }

    fn after_parsing<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        let external_annotations =
            if let Some(annotation_file) = self.opts.modelctrl().external_annotations() {
                toml::from_str(
                    &std::fs::read_to_string(annotation_file).unwrap_or_else(|_| {
                        panic!(
                            "Could not open file {}/{}",
                            std::env::current_dir().unwrap().display(),
                            annotation_file.display()
                        )
                    }),
                )
                .unwrap()
            } else {
                HashMap::new()
            };
        queries
            .global_ctxt()
            .unwrap()
            .take()
            .enter(|tcx| {
                let desc = discover::CollectingVisitor::new(tcx, self.opts, &external_annotations).run()?;
                if self.opts.dbg().dump_serialized_flow_graph() {
                    serde_json::to_writer(
                        &mut std::fs::OpenOptions::new()
                            .truncate(true)
                            .create(true)
                            .write(true)
                            .open(consts::FLOW_GRAPH_OUT_NAME)
                            .unwrap(),
                        &desc,
                    )
                    .unwrap();
                }
                info!("All elems walked");
                let result_path = compiler
                    .build_output_filenames(&*compiler.session(), &[])
                    .with_extension("ana.frg");
                let mut outf = outfile_pls(&result_path)?;
                let doc_alloc = pretty::BoxAllocator;
                let doc: DocBuilder<_, ()> = desc.serialize_forge(&doc_alloc, tcx, self.opts.modelctrl().model_version());
                doc.render(100, &mut outf)?;
                let mut outf_2 = outfile_pls(self.opts.result_path())?;
                doc.render(100, &mut outf_2)?;

                let info_path = compiler.build_output_filenames(&*compiler.session(), &[])
                    .with_extension("info.json");
                let info = AdditionalInfo {
                    call_sites: desc.all_call_sites().into_iter().map(|cs| (cs.to_string(), cs.clone())).collect()
                };
                serde_json::to_writer(outfile_pls(info_path)?, &info)?;

                let info_path2 = self.opts.result_path().with_extension("info.json");

                serde_json::to_writer(outfile_pls(info_path2)?, &info)?;
                warn!("Due to potential overwrite issues with --result-path (with multiple targets in a crate) outputs were written to {} and {}", self.opts.result_path().display(), &result_path.display());
                Ok::<_, std::io::Error>(
                    if self.opts.abort_after_analysis() {
                        rustc_driver::Compilation::Stop
                    } else {
                        rustc_driver::Compilation::Continue
                    }
                )
            })
            .unwrap()
    }
}

impl rustc_plugin::RustcPlugin for DfppPlugin {
    type Args = Args;

    fn bin_name() -> String {
        "dfpp".to_string()
    }

    fn args(
        &self,
        _target_dir: &rustc_plugin::Utf8Path,
    ) -> rustc_plugin::RustcPluginArgs<Self::Args> {
        use clap::Parser;
        let args = ArgWrapper::parse();
        rustc_plugin::RustcPluginArgs {
            args: args.args,
            file: None,
            flags: None,
            cargo_args: args.cargo_args,
        }
    }

    fn run(
        self,
        compiler_args: Vec<String>,
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

        if let Some(k) = compiler_args
            .iter()
            .enumerate()
            .find_map(|(i, s)| (s == "--crate-name").then_some(i))
        {
            if let Some(s) = compiler_args.get(k + 1) {
                if plugin_args.target().map_or(false, |t| t != s) {
                    return rustc_driver::RunCompiler::new(&compiler_args, &mut NoopCallbacks {})
                        .run();
                }
            }
        }

        let lvl = if plugin_args.debug().is_enabled() {
            log::LevelFilter::Debug
        } else if plugin_args.verbose() {
            log::LevelFilter::Info
        } else {
            log::LevelFilter::Warn
        };
        // //let lvl = log::LevelFilter::Debug;
        simple_logger::SimpleLogger::new()
            .with_level(lvl)
            .with_module_level("flowistry", log::LevelFilter::Error)
            .without_timestamps()
            .init()
            .unwrap();
        if matches!(*plugin_args.debug(), LogLevelConfig::Targeted(..)) {
            log::set_max_level(if plugin_args.verbose() {
                log::LevelFilter::Info
            } else {
                log::LevelFilter::Warn
            });
        }
        let opts = Box::leak(Box::new(plugin_args));
        rustc_driver::RunCompiler::new(&compiler_args, &mut Callbacks { opts }).run()
    }
}
