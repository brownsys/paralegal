#![feature(rustc_private)]

#[macro_use]
extern crate clap;
extern crate ordermap;
extern crate rustc_plugin;
extern crate serde;
#[macro_use]
extern crate lazy_static;
extern crate simple_logger;
#[macro_use]
extern crate log;

pub mod rust {
    pub extern crate rustc_ast;
    pub extern crate rustc_data_structures;
    pub extern crate rustc_driver;
    pub extern crate rustc_hir;
    pub extern crate rustc_interface;
    pub extern crate rustc_middle;
    pub extern crate rustc_mir_dataflow;
    pub extern crate rustc_query_system;
    pub extern crate rustc_span;

    pub use rustc_ast as ast;
    pub use rustc_hir as hir;
    pub use rustc_middle::mir;

    pub use rustc_middle::dep_graph::DepGraph;
}

use rust::*;

use clap::Parser;
use flowistry::mir::borrowck_facts;
pub use std::collections::{HashMap, HashSet};

pub use rustc_span::Symbol;

mod dbg;
mod ana;
pub mod ann_parse;
pub mod desc;
mod frg;
mod sah;

use ana::AttrMatchT;

use frg::ToForge;

macro_rules! sym_vec {
    ($($e:expr),*) => {
        vec![$(Symbol::intern($e)),*]
    };
}

pub struct DfppPlugin;

#[derive(serde::Serialize, serde::Deserialize, Parser)]
pub struct Args {
    /// This argument doesn't do anything, but when cargo invokes `cargo-dfpp`
    /// it always provides "dfpp" as the first argument and since we parse with
    /// clap it otherwise complains about the superfluous argument.
    _progname: String,
    #[clap(short, long)]
    verbose: bool,
    #[clap(long)]
    debug: bool,
    #[clap(long, default_value = "analysis_result.frg")]
    result_path: std::path::PathBuf,
    #[clap(long)]
    dump_flowistry_matrix: bool,
}

struct Callbacks {
    opts: &'static Args,
}

lazy_static! {
    static ref LABEL_MARKER: AttrMatchT = sym_vec!["dfpp", "label"];
    static ref ANALYZE_MARKER: AttrMatchT = sym_vec!["dfpp", "analyze"];
    static ref OTYPE_MARKER: AttrMatchT = sym_vec!["dfpp", "output_types"];
    static ref EXCEPTION_MARKER: AttrMatchT = sym_vec!["dfpp", "exception"];
}

impl rustc_driver::Callbacks for Callbacks {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        config.override_queries = Some(borrowck_facts::override_queries);
    }

    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        let desc = queries
            .global_ctxt()
            .unwrap()
            .take()
            .enter(|tcx| ana::Visitor::new(tcx, self.opts).run())
            .unwrap();
        info!("All elems walked");
        let mut outf = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(&self.opts.result_path)
            .unwrap();
        let doc_alloc = pretty::BoxAllocator;
        let doc = desc.as_forge(&doc_alloc);
        doc.render(100, &mut outf).unwrap();
        info!(
            "Wrote analysis result to {}",
            &self.opts.result_path.canonicalize().unwrap().display()
        );
        rustc_driver::Compilation::Stop
    }
}

lazy_static! {
    static ref ARG_SYM: Symbol = Symbol::intern("arguments");
    static ref RETURN_SYM: Symbol = Symbol::intern("return");
    static ref VERIFICATION_HASH_SYM: Symbol = Symbol::intern("verification_hash");
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
        rustc_plugin::RustcPluginArgs {
            args: Args::parse(),
            file: None,
            flags: None,
        }
    }

    fn run(
        self,
        compiler_args: Vec<String>,
        plugin_args: Self::Args,
    ) -> rustc_interface::interface::Result<()> {
        let lvl = if plugin_args.debug {
            log::LevelFilter::Debug
        } else if plugin_args.verbose {
            log::LevelFilter::Info
        } else {
            log::LevelFilter::Warn
        };
        simple_logger::SimpleLogger::new()
            .with_level(lvl)
            .with_module_level("flowistry", log::LevelFilter::Error)
            .init()
            .unwrap();
        let opts = Box::leak(Box::new(plugin_args));
        rustc_driver::RunCompiler::new(&compiler_args, &mut Callbacks { opts }).run()
    }
}
