#![feature(rustc_private)]

extern crate clap;
extern crate serde;

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_plugin;
extern crate rustc_span;

use clap::Parser;
use flowistry::{infoflow, mir::borrowck_facts};
use rustc_hir::{
    hir_id::HirId,
    intravisit::{self, FnKind},
    BodyId,
};
use rustc_middle::{hir::nested_filter::OnlyBodies, ty::TyCtxt};
use rustc_span::{symbol::Ident, Span};

struct DfppPlugin;

#[derive(serde::Serialize, serde::Deserialize, Parser)]
struct Args {}

struct Callbacks;

impl rustc_driver::Callbacks for Callbacks {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        config.override_queries = Some(borrowck_facts::override_queries);
    }

    fn after_parsing<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        queries.global_ctxt().unwrap().take().enter(|tcx| {
            let mut visitor = Visitor { tcx };
            tcx.hir().deep_visit_all_item_likes(&mut visitor);
        });
        rustc_driver::Compilation::Stop
    }
}

pub struct Visitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Visitor<'tcx> {
    fn is_interesting(&self, ident: &Ident) -> bool {
        ["answers"].contains(&ident.as_str())
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for Visitor<'tcx> {
    type NestedFilter = OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_fn(
        &mut self,
        fk: FnKind<'tcx>,
        fd: &'tcx rustc_hir::FnDecl<'tcx>,
        b: BodyId,
        s: Span,
        id: HirId,
    ) {
        if match &fk {
            FnKind::ItemFn(ident, _, _) | FnKind::Method(ident, _) => self.is_interesting(ident),
            _ => false,
        } {
            let tcx = self.tcx;
            let local_def_id = tcx.hir().body_owner_def_id(b);
            let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, local_def_id);
            let flow = infoflow::compute_flow(tcx, b, body_with_facts);
            let loc_dom = flow.analysis.location_domain();
            use flowistry::indexed::IndexedDomain;
            for loc in loc_dom.as_vec().iter() {
                let matrix = flow.state_at(*loc);
                for (r, deps) in matrix.rows() {
                    println!("{:?}:", r);
                    for loc in deps.iter() {
                        println!("  {:?}", loc);
                    }
                }
            }
        };

        // dispatch to recursive walk. This is probably unnecessary but if in
        // the future we decide to do something with nested items we may need
        // it.
        intravisit::walk_fn(self, fk, fd, b, s, id)
    }
}

impl rustc_plugin::RustcPlugin for DfppPlugin {
    type Args = Args;

    fn bin_name() -> String {
        "df++".to_string()
    }

    fn args(
        &self,
        target_dir: &rustc_plugin::Utf8Path,
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
        rustc_driver::RunCompiler::new(&compiler_args, &mut Callbacks).run()
    }
}

fn main() {
    eprintln!("Hello!");
    rustc_plugin::driver_main(DfppPlugin);
}
