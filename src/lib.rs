#![feature(rustc_private)]

extern crate clap;
extern crate rustc_plugin;
extern crate serde;

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use clap::Parser;
use flowistry::{
    infoflow,
    mir::{
        borrowck_facts,
        utils::{location_to_string, BodyExt},
    },
};
use std::collections::HashSet;

use rustc_hir::{
    self as hir,
    def_id::DefId,
    hir_id::HirId,
    intravisit::{self, FnKind},
    BodyId,
};
use rustc_middle::{
    hir::nested_filter::OnlyBodies,
    mir,
    ty::{self, TyCtxt},
};
use rustc_span::{symbol::Ident, Span, Symbol};

type AttrMatchT = Vec<Symbol>;

trait MetaItemMatch {
    fn matches_path(&self, p: &[Symbol]) -> bool;
}

impl MetaItemMatch for rustc_ast::ast::Attribute {
    fn matches_path(&self, p: &[Symbol]) -> bool {
        match &self.kind {
            rustc_ast::ast::AttrKind::Normal(
                rustc_ast::ast::AttrItem {
                    args: rustc_ast::ast::MacArgs::Empty,
                    path,
                    ..
                },
                _,
            ) => {
                path.segments.len() == p.len()
                    && path
                        .segments
                        .iter()
                        .zip(p)
                        .all(|(seg, i)| seg.ident.name == *i)
            }
            _ => false,
        }
    }
}

macro_rules! sym_vec {
    ($($e:expr),*) => {
        vec![$(Symbol::intern($e)),*]
    };
}

pub struct DfppPlugin;

#[derive(serde::Serialize, serde::Deserialize, Parser)]
pub struct Args {}

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
            Visitor::new(
                tcx,
                sym_vec!["dfpp", "sink"],
                sym_vec!["dfpp", "source"],
                sym_vec!["dfpp", "analyze"],
                sym_vec!["dfpp", "auth_witness"],
            )
            .run();
        });
        println!("All elems walked");
        rustc_driver::Compilation::Stop
    }
}

fn called_fn<'tcx>(call: &mir::terminator::Terminator<'tcx>) -> Option<DefId> {
    match &call.kind {
        mir::terminator::TerminatorKind::Call { func, .. } => {
            if let Some(mir::Constant {
                literal: mir::ConstantKind::Val(_, ty),
                ..
            }) = func.constant()
            {
                match ty.kind() {
                    ty::FnDef(defid, _) => Some(*defid),
                    _ => None,
                }
            } else {
                None
            }
        }
        _ => None,
    }
}

fn ty_def(ty: &ty::Ty) -> Option<DefId> {
    match ty.kind() {
        ty::TyKind::Adt(def, _) => Some(def.did()),
        ty::TyKind::Foreign(did) 
        | ty::TyKind::FnDef(did, _)
        | ty::TyKind::Closure(did, _)
        | ty::TyKind::Generator(did, _, _)
        | ty::TyKind::Opaque(did, _) => Some(*did),
        _ => None,
    }
}

fn type_has_ann(tcx: TyCtxt, auth_witness_marker: &AttrMatchT, ty: &ty::Ty) -> bool {
    ty.walk().any(|generic|
        if let ty::subst::GenericArgKind::Type(ty) = generic.unpack() {
            ty_def(&ty).and_then(DefId::as_local).map_or(false, |def|
                tcx.hir().attrs(tcx.hir().local_def_id_to_hir_id(def))
                .iter()
                .any(|a| a.matches_path(auth_witness_marker)))
            
        } else {
            false
        }
    )
}

fn extract_places<'tcx>(t: &mir::Terminator<'tcx>, loc: mir::Location) -> HashSet<mir::Place<'tcx>> {
    struct Visitor<'tcx>(HashSet<mir::Place<'tcx>>);
    impl <'tcx> mir::visit::Visitor<'tcx> for Visitor<'tcx> {
        fn visit_place(&mut self, place: &mir::Place<'tcx>, _ctx: mir::visit::PlaceContext, location: mir::Location) {
            self.0.insert(*place);
        }
    }
    let mut vis = Visitor(HashSet::new());
    use mir::visit::MirVisitable;
    t.apply(loc, &mut vis);
    vis.0
}

pub struct Visitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    sink_marker: AttrMatchT,
    source_marker: AttrMatchT,
    analyze_marker: AttrMatchT,
    auth_witness_marker: AttrMatchT,
    marked_sinks: HashSet<HirId>,
    marked_sources: HashSet<HirId>,
    functions_to_analyze: Vec<(Ident, BodyId, &'tcx rustc_hir::FnDecl<'tcx>)>,
}

impl<'tcx> Visitor<'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        sink_marker: AttrMatchT,
        source_marker: AttrMatchT,
        analyze_marker: AttrMatchT,
        auth_witness_marker: AttrMatchT,
    ) -> Self {
        Self {
            tcx,
            sink_marker,
            source_marker,
            analyze_marker,
            auth_witness_marker,
            marked_sinks: HashSet::new(),
            marked_sources: HashSet::new(),
            functions_to_analyze: vec![],
        }
    }

    fn is_interesting_fn(&self, ident: HirId) -> bool {
        self.tcx
            .hir()
            .attrs(ident)
            .iter()
            .any(|a| a.matches_path(&self.analyze_marker))
    }


    fn run(&mut self) {
        let tcx = self.tcx;
        tcx.hir().deep_visit_all_item_likes(self);
        //println!("{:?}\n{:?}\n{:?}", self.marked_sinks, self.marked_sources, self.functions_to_analyze);
        self.analyze();
    }

    fn analyze(&mut self) {
        let mut targets = std::mem::replace(&mut self.functions_to_analyze, vec![]);
        let tcx = self.tcx;
        let sink_fn_defs = self
            .marked_sinks
            .iter()
            .map(|s| tcx.hir().local_def_id(*s).to_def_id())
            .collect::<HashSet<_>>();
        let source_fn_defs = self
            .marked_sources
            .iter()
            .map(|s| tcx.hir().local_def_id(*s).to_def_id())
            .collect::<HashSet<_>>();
        println!(
            "Analysis begin:\n  {} targets\n  {} marked sinks\n  {} marked sources",
            targets.len(),
            sink_fn_defs.len(),
            source_fn_defs.len()
        );
        for (id, b, fd) in targets.drain(..) {
            let mut called_fns_found = 0;
            let mut source_fns_found = 0;
            let mut sink_fn_defs_found = 0;
            let local_def_id = tcx.hir().body_owner_def_id(b);
            let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, local_def_id);
            use flowistry::indexed::{impls::LocationDomain, IndexedDomain};
            let body = &body_with_facts.body;
            let loc_dom = LocationDomain::new(body);
            println!("{}", id.as_str());
            let mut source_locs = body
                .args_iter()
                .filter_map(|l| {
                    if type_has_ann(tcx, &self.auth_witness_marker, &body.local_decls[l].ty) {
                        Some(*loc_dom.value(loc_dom.arg_to_location(l)))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            let source_args_found = source_locs.len();
            let flow = infoflow::compute_flow(tcx, b, body_with_facts);
            for (bb, bbdat) in body.basic_blocks().iter_enumerated() {
                let loc = body.terminator_loc(bb);
                if let Some((t, p)) = bbdat.terminator.as_ref().and_then(|t| called_fn(t).map(|p| (t, p))) {
                    called_fns_found += 1;
                    if source_fn_defs.contains(&p) {
                        source_fns_found += 1;
                        source_locs.push(loc);
                    }
                    if sink_fn_defs.contains(&p) {
                        let mentioned_places = extract_places(t, loc);
                        sink_fn_defs_found += 1;
                        let matrix = flow.state_at(loc);
                        for r in mentioned_places.iter() {
                            let deps = matrix.row(*r);
                            let mut header_printed = false;
                            for loc in deps.filter(|l| source_locs.contains(l)) {
                                if !header_printed { println!("  {:?}:", r); header_printed = true };
                                print!("    ");
                                println!("{}", location_to_string(*loc, body));
                            }
                        }
                    }
                };
            }
            println!("Function {}:\n  {} called functions found\n  {} source args found\n  {} source fns matched\n  {} sink fns matched", id, called_fns_found, source_args_found, source_fns_found, sink_fn_defs_found);
        }
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for Visitor<'tcx> {
    type NestedFilter = OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_id(&mut self, id: HirId) {
        if self
            .tcx
            .hir()
            .attrs(id)
            .iter()
            .any(|a| a.matches_path(&self.sink_marker))
        {
            self.marked_sinks.insert(id);
        }
        if self
            .tcx
            .hir()
            .attrs(id)
            .iter()
            .any(|a| a.matches_path(&self.source_marker))
        {
            self.marked_sources.insert(id);
        }
    }

    fn visit_fn(
        &mut self,
        fk: FnKind<'tcx>,
        fd: &'tcx rustc_hir::FnDecl<'tcx>,
        b: BodyId,
        s: Span,
        id: HirId,
    ) {
        match &fk {
            FnKind::ItemFn(ident, _, _) | FnKind::Method(ident, _)
                if self.is_interesting_fn(id) =>
            {
                self.functions_to_analyze.push((*ident, b, fd));
            }
            _ => (),
        }

        // dispatch to recursive walk. This is probably unnecessary but if in
        // the future we decide to do something with nested items we may need
        // it.
        intravisit::walk_fn(self, fk, fd, b, s, id)
    }
}

impl rustc_plugin::RustcPlugin for DfppPlugin {
    type Args = Args;

    fn bin_name() -> String {
        "dfpp".to_string()
    }

    fn args(
        &self,
        target_dir: &rustc_plugin::Utf8Path,
    ) -> rustc_plugin::RustcPluginArgs<Self::Args> {
        rustc_plugin::RustcPluginArgs {
            args: Args {},
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
