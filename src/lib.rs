#![feature(rustc_private)]

#[macro_use]
extern crate clap;
extern crate ordermap;
extern crate rustc_plugin;
extern crate serde;
#[macro_use]
extern crate trait_enum;
#[macro_use]
extern crate lazy_static;

pub mod rust {
    pub extern crate rustc_ast;
    pub extern crate rustc_data_structures;
    pub extern crate rustc_driver;
    pub extern crate rustc_hir;
    pub extern crate rustc_interface;
    pub extern crate rustc_middle;
    pub extern crate rustc_span;

    pub use rustc_ast as ast;
    pub use rustc_hir as hir;
    pub use rustc_middle::mir;
}

use rust::*;

use clap::Parser;
use flowistry::mir::borrowck_facts;
pub use std::collections::{HashMap, HashSet};
use std::io::{Sink, Stdout, Write};
use std::ops::DerefMut;

pub use rustc_span::Symbol;

mod ana;
mod ann_parse;
mod desc;
mod frg;

use ana::AttrMatchT;

use frg::ToForge;

trait_enum! {
    enum Printers : Write {
        Stdout,
        Sink,
    }
}

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
    #[clap(long, default_value = "analysis_result.frg")]
    result_path: std::path::PathBuf,
}

struct Callbacks {
    printer: Printers,
    res_p: std::path::PathBuf,
}

lazy_static! {
    static ref LABEL_MARKER: AttrMatchT = sym_vec!["dfpp", "label"];
    static ref ANALYZE_MARKER: AttrMatchT = sym_vec!["dfpp", "analyze"];
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
            .enter(|tcx| ana::Visitor::new(tcx, &mut self.printer).run())
            .unwrap();
        writeln!(self.printer.deref_mut(), "All elems walked").unwrap();
        let mut outf = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(&self.res_p)
            .unwrap();
        use pretty::DocAllocator;
        let doc_alloc = pretty::BoxAllocator;
        let doc = desc.as_forge(&doc_alloc);
        doc.render(100, &mut outf).unwrap();
        writeln!(
            self.printer.deref_mut(),
            "Wrote analysis result to {}",
            &self.res_p.canonicalize().unwrap().display()
        )
        .unwrap();
        rustc_driver::Compilation::Stop
    }
}

lazy_static! {
    static ref LEAKS_SYM: Symbol = Symbol::intern("leaks");
    static ref SCOPED_SYM: Symbol = Symbol::intern("scopes");
    static ref ARG_SYM: Symbol = Symbol::intern("arguments");
    static ref SINK_ANN_SYMS: HashSet<Symbol> = [*LEAKS_SYM, *SCOPED_SYM].into_iter().collect();
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
        let printer = if plugin_args.verbose {
            Printers::Stdout(std::io::stdout())
        } else {
            Printers::Sink(std::io::sink())
        };
        let res_p = plugin_args.result_path;
        rustc_driver::RunCompiler::new(&compiler_args, &mut Callbacks { printer, res_p }).run()
    }
}
