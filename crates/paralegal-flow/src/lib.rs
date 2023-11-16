//! Ties together the crate and defines command line options.
//!
//! While this is technically a "library", it only is so for the purposes of
//! being able to reference the same code in the two executables `paralegal_flow` and
//! `cargo-paralegal-flow` (a structure suggested by [rustc_plugin]).
#![feature(
    rustc_private,
    min_specialization,
    drain_filter,
    box_patterns,
    let_chains
)]

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
extern crate num_derive;
extern crate num_traits;
extern crate petgraph;

#[macro_use]
pub extern crate rustc_index;
extern crate rustc_serialize;

pub mod rust {
    //! Exposes the rustc external crates (this mod is just to tidy things up).
    pub extern crate rustc_abi;
    pub extern crate rustc_arena;
    pub extern crate rustc_ast;
    pub extern crate rustc_borrowck;
    pub extern crate rustc_data_structures;
    pub extern crate rustc_driver;
    pub extern crate rustc_error_messages;
    pub extern crate rustc_hir;
    pub extern crate rustc_interface;
    pub extern crate rustc_middle;
    pub extern crate rustc_mir_dataflow;
    pub extern crate rustc_query_system;
    pub extern crate rustc_serialize;
    pub extern crate rustc_span;
    pub extern crate rustc_target;
    pub extern crate rustc_type_ir;
    pub use super::rustc_index;
    pub use rustc_type_ir::sty;

    pub use rustc_ast as ast;
    pub mod mir {
        pub use super::rustc_abi::FieldIdx as Field;
        pub use super::rustc_middle::mir::*;
    }
    pub use rustc_hir as hir;
    pub use rustc_middle::ty;

    pub use rustc_middle::dep_graph::DepGraph;
    pub use ty::TyCtxt;

    pub use hir::def_id::{DefId, LocalDefId};
    pub use hir::BodyId;
    pub use mir::Location;
    pub use rustc_span::Span;
}

use args::{ClapArgs, LogLevelConfig};
use desc::utils::{serde_map_via_vec, write_sep};
use pretty::DocBuilder;
use rust::*;

use rustc_plugin::CrateFilter;
use rustc_utils::mir::borrowck_facts;
pub use std::collections::{HashMap, HashSet};
use std::fmt::Display;

// This import is sort of special because it comes from the private rustc
// dependencies and not from our `Cargo.toml`.
pub extern crate either;
pub use either::Either;

pub use rustc_span::Symbol;

pub mod ana;
pub mod ann_parse;
mod args;
pub mod dbg;
mod discover;
pub mod frg;
pub mod ir;
//mod sah;
pub mod serializers;
#[macro_use]
pub mod utils;
pub mod consts;
pub mod marker_db;
#[cfg(feature = "test")]
pub mod test_utils;

pub use paralegal_spdg as desc;

pub use args::{AnalysisCtrl, Args, BuildConfig, DepConfig, DumpArgs, ModelCtrl};

use crate::{
    frg::{call_site_to_string, ForgeConverter},
    utils::{outfile_pls, Print},
};

pub use crate::marker_db::MarkerCtx;

/// A struct so we can implement [`rustc_plugin::RustcPlugin`]
pub struct DfppPlugin;

/// Top level argument structure. This is only used for parsing. The actual
/// configuration of paralegal-flow [`struct@Args`] which is stored in `args`. `cargo_args` is
/// forwarded and `_progname` is only to comply with the calling convention of
/// `cargo` (it passes the program name as first argument).
#[derive(clap::Parser)]
#[clap(version = concat!(crate_version!(), "\nbuilt ", env!("BUILD_TIME"), "\ncommit ", env!("COMMIT_HASH")), about)]
struct ArgWrapper {
    /// This argument doesn't do anything, but when cargo invokes `cargo-paralegal-flow`
    /// it always provides "paralegal-flow" as the first argument and since we parse with
    /// clap it otherwise complains about the superfluous argument.
    _progname: String,

    /// The actual arguments
    #[clap(flatten)]
    args: ClapArgs,

    /// Pass through for additional cargo arguments (like --features)
    #[clap(last = true)]
    cargo_args: Vec<String>,
}

struct Callbacks {
    opts: &'static Args,
}

struct NoopCallbacks {}

impl rustc_driver::Callbacks for NoopCallbacks {}

#[derive(serde::Deserialize, serde::Serialize)]
pub struct AdditionalInfo {
    #[serde(with = "serde_map_via_vec")]
    pub call_sites: HashMap<String, desc::CallSite>,
}

#[cfg(feature = "profiling")]
mod flame_dump {
    use crate::InlinerSize;

    pub fn dump(memory_root: &dyn allocative::Allocative) {
        println!("Dumping timing flamegraph");
        match std::fs::File::create("time-flamegraph.html") {
            Err(e) => println!("Couldn't create timing flamegraph file: {e}"),
            Ok(f) => {
                if let Err(e) = flame::dump_html(f) {
                    println!("Couldn't dump timing flamegraph: {e}")
                }
            }
        }

        dump_memory(
            [
                memory_root,
                &InlinerSize::<paralegal_spdg::global_location::RawGlobalLocation>(
                    std::marker::PhantomData,
                ),
            ],
            None,
        );
    }

    pub fn dump_memory<'a>(
        roots: impl IntoIterator<Item = &'a dyn allocative::Allocative>,
        prefix: Option<&str>,
    ) {
        let mut name = String::new();
        if let Some(prefix) = prefix {
            use std::fmt::Write;
            write!(name, "{}-", prefix).unwrap();
        }
        name.push_str("memory-flamegraph.folded");
        match std::fs::File::create(name) {
            Err(e) => println!("Couldn't create memory flamegraph file: {e}"),
            Ok(mut f) => {
                use std::io::Write;
                let mut vis = allocative::FlameGraphBuilder::default();
                let total_size: usize = roots
                    .into_iter()
                    .map(|root| {
                        vis.visit_root(root);
                        allocative::size_of_unique_allocated_data(root)
                    })
                    .sum();
                print!("Total size of ");
                if let Some(prefix) = prefix {
                    print!("{prefix} ");
                }
                println!("memory dump: {total_size} bytes");
                write!(f, "{}", vis.finish_and_write_flame_graph()).unwrap();
            }
        }
    }
}

struct InlinerSize<T>(std::marker::PhantomData<T>);

impl<T: Eq + std::hash::Hash + Send + Sync + 'static> allocative::Allocative for InlinerSize<T> {
    fn visit<'a, 'b: 'a>(&self, visitor: &'a mut allocative::Visitor<'b>) {
        let key: allocative::Key =
            allocative::Key::new(std::any::type_name::<internment::Intern<T>>());
        visitor
            .enter(
                key,
                internment::Intern::<T>::num_objects_interned() * std::mem::size_of::<T>(),
            )
            .exit()
    }
}

impl rustc_driver::Callbacks for Callbacks {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        config.override_queries = Some(borrowck_facts::override_queries);
    }

    #[cfg_attr(feature = "profiling", flamer::flame)]
    // This used to run `after_parsing` but that now makes `tcx.crates()` empty
    // (which interferes with external annotation resolution). So now it runs
    // `after_expansion` and so far that doesn't seem to break anything, but I'm
    // explaining this here in case that flowistry has some sort of issue with
    // that (when retrieving the MIR bodies for instance)
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        queries
            .global_ctxt()
            .unwrap()
            .enter(|tcx| {
                tcx.sess.abort_if_errors();
                let desc = discover::CollectingVisitor::new(tcx, self.opts).run()?;
                if self.opts.dbg().dump_serialized_flow_graph() {
                    serde_json::to_writer(
                        &mut std::fs::OpenOptions::new()
                            .truncate(true)
                            .create(true)
                            .write(true)
                            .open(self.opts.graph_loc_path.clone())
                            .unwrap(),
                        &desc,
                    )
                    .unwrap();
                }
                tcx.sess.abort_if_errors();
                info!("All elems walked");
                let result_path = compiler
                    .build_output_filenames(compiler.session(), &[])
                    .with_extension("ana.frg");
                let mut outf = outfile_pls(&result_path)?;
                let doc_alloc = pretty::BoxAllocator;
                let converter = ForgeConverter::new(desc, tcx);
                let doc: DocBuilder<_, ()> = converter.serialize_forge(&doc_alloc, self.opts.modelctrl());
                doc.render(100, &mut outf)?;
                let mut outf_2 = outfile_pls(self.opts.result_path())?;
                doc.render(100, &mut outf_2)?;

                let info_path = compiler.build_output_filenames(compiler.session(), &[])
                    .with_extension("info.json");
                let info = AdditionalInfo {
                    call_sites: converter.desc().all_call_sites().into_iter().map(|cs| (call_site_to_string(tcx, cs), cs.clone())).collect()
                };
                serde_json::to_writer(outfile_pls(info_path)?, &info)?;

                let info_path2 = self.opts.result_path().with_extension("info.json");

                serde_json::to_writer(outfile_pls(info_path2)?, &info)?;
                warn!("Due to potential overwrite issues with --result-path (with multiple targets in a crate) outputs were written to {} and {}", self.opts.result_path().display(), &result_path.display());
                anyhow::Ok(
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
        // This is actually not necessary for *this* binary, but it will bne
        // inherited by the calls to `cargo` and `rustc` does by `rustc_plugin`
        // and thus those will link against the version of `std` that we
        // require.
        std::env::set_var("SYSROOT", env!("SYSROOT_PATH"));

        add_to_rustflags(["--cfg".into(), "paralegal".into()]).unwrap();

        rustc_plugin::RustcPluginArgs {
            args: args.args.try_into().unwrap(),
            filter: CrateFilter::AllCrates,
            cargo_args: args.cargo_args,
        }
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

        let is_target = crate_name
            .as_ref()
            .and_then(|s| plugin_args.target().map(|t| s == t))
            .unwrap_or(is_primary_package);

        let is_build_script = crate_name
            .as_ref()
            .map_or(false, |n| n == "build_script_build");

        if !is_target || is_build_script {
            return rustc_driver::RunCompiler::new(&compiler_args, &mut NoopCallbacks {}).run();
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
            .with_module_level("rustc_utils", log::LevelFilter::Error)
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

        compiler_args.extend([
            "--cfg".into(),
            "paralegal".into(),
            "-Zcrate-attr=feature(register_tool)".into(),
            "-Zcrate-attr=register_tool(paralegal_flow)".into(),
        ]);

        debug!(
            "Arguments: {}",
            Print(|f| write_sep(f, " ", &compiler_args, Display::fmt))
        );
        rustc_driver::RunCompiler::new(&compiler_args, &mut Callbacks { opts }).run()
    }
}
