#![feature(rustc_private)]

extern crate clap;
extern crate ordermap;
extern crate rustc_plugin;
extern crate serde;
#[macro_use]
extern crate trait_enum;
#[macro_use]
extern crate lazy_static;
extern crate pretty;

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
use ordermap::OrderSet;
use std::collections::{HashMap, HashSet};
use std::io::{Sink, Stdout, Write};
use std::ops::DerefMut;

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

trait_enum! {
    enum Printers : Write {
        Stdout,
        Sink,
    }
}

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
pub struct Args {
    /// This argument doesn't do anything, but when cargo invokes `cargo-dfpp`
    /// it always provides "dfpp" as the first argument and since we parse with
    /// clap it otherwise complains about the superfluous argument.
    _progname: String,
    #[clap(short, long)]
    verbose: bool,
    #[clap(long, default_value = "analysis_result.txt")]
    result_path: std::path::PathBuf,
}

type Endpoint = Identifier;

struct ProgramDescription {
    d: HashMap<Endpoint, DfGraph>,
}

trait ToForge {
    fn as_forge<'b, 'a : 'b, A: pretty::DocAllocator<'b, ()>>(&'a self, alloc: &'b A) -> pretty::DocBuilder<'b, A, ()> 
    where A::Doc: Clone;
}


impl ProgramDescription {
    fn empty() -> Self {
        ProgramDescription { d: HashMap::new() }
    }
}

impl ToForge for Identifier {
    fn as_forge<'b, 'a : 'b, A: pretty::DocAllocator<'b, ()>>(&'a self, alloc: &'b A) -> pretty::DocBuilder<'b, A, ()> 
    where A::Doc: Clone {
        alloc.text(&self.0)
    }
}

impl <X: ToForge, Y:ToForge> ToForge for Relation<X,Y> {
    fn as_forge<'b, 'a : 'b, A: pretty::DocAllocator<'b, ()>>(&'a self, alloc: &'b A) -> pretty::DocBuilder<'b, A, ()> 
    where A::Doc: Clone {
        alloc.intersperse(
            self.0.iter().map(|(src, sinks)|
                src.as_forge(alloc)
                    .append("->")
                    .append(
                        alloc.intersperse(
                            sinks.iter().map(|sink| sink.as_forge(alloc)), alloc.text(" + ")).parens())
            ),
            alloc.text(" +").append(alloc.hardline())
        )
    }
}

impl ToForge for DataSink {
    fn as_forge<'b, 'a : 'b, A: pretty::DocAllocator<'b, ()>>(&'a self, alloc: &'b A) -> pretty::DocBuilder<'b, A, ()> 
    where A::Doc: Clone {
        self.function.as_forge(alloc).append(alloc.text("_")).append(alloc.as_string(self.arg_slot))
    }
}


impl ToForge for ProgramDescription {
    fn as_forge<'b, 'a : 'b, A: pretty::DocAllocator<'b, ()>>(&'a self, alloc: &'b A) -> pretty::DocBuilder<'b, A, ()> 
    where A::Doc: Clone
    {
        alloc.intersperse(
            self.d.iter().map(|(e, g)| 
                alloc.as_string(e)
                    .append(" = ")
                    .append(
                        alloc.hardline()
                        .append(
                            g.g.as_forge(alloc).indent(4)
                        )
                        .parens()
                    )
            ),
            alloc.hardline()
        )
    }
}

impl ProgramDescription {
    fn ser_frg<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        for (e, g) in self.d.iter() {
            writeln!(w, "{e} = (")?;
            let mut first_src = true;
            for (src, sinks) in g.g.0.iter() {
                if sinks.is_empty() { continue; }
                if first_src { first_src = false }
                else { write!(w, " +")?}
                writeln!(w, "  {src}->(")?;
                let mut first_sink = true;
                for sink in sinks.iter() {
                    if first_sink { first_sink = false }
                    else { writeln!(w, " +")?; }
                    write!(w, "    {sink}_{sn}", sink=sink.function, sn= sink.arg_slot)?;
                }
                writeln!(w, ")")?;
            }
            writeln!(w, ")")?;
        }
        Ok(())
    }
}

#[derive(Hash, Eq, PartialEq, Ord, Debug, PartialOrd, Clone)]
struct Identifier(String);

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.0.fmt(f)
    }
}

struct Relation<X, Y>(HashMap<X, HashSet<Y>>);

impl<X, Y> Relation<X, Y> {
    fn empty() -> Self {
        Relation(HashMap::new())
    }
}

type DataSource = Identifier;

#[derive(Hash, PartialEq, Eq, PartialOrd, Ord)]
struct DataSink { 
    function: Identifier,
    arg_slot: usize
}

struct DfGraph {
    g: Relation<DataSource, DataSink>,
}

impl DfGraph {
    fn empty() -> Self {
        DfGraph {
            g: Relation::empty(),
        }
    }
    fn add(&mut self, from: &DataSource, to: DataSink) {
        let m = &mut self.g.0;
        if let Some(e) = m.get_mut(from) {
            e.insert(to);
        } else {
            m.insert(from.clone(), std::iter::once(to).collect());
        }
    }
}

struct Callbacks {
    printer: Printers,
    res_p: std::path::PathBuf,
}

lazy_static! {
    static ref SINK_MARKER: AttrMatchT = sym_vec!["dfpp", "sink"];
    static ref SOURCE_MARKER: AttrMatchT = sym_vec!["dfpp", "source"];
    static ref ANALYZE_MARKER: AttrMatchT = sym_vec!["dfpp", "analyze"];
    static ref AUTH_WITNESS_MARKER: AttrMatchT = sym_vec!["dfpp", "auth_witness"];
    static ref SENSITIVE_MARKER: AttrMatchT = sym_vec!["dfpp", "sensitive"];
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
        let res = queries.global_ctxt().unwrap().take().enter(|tcx| {
            Visitor::new(tcx, &mut self.printer).run()
        }).unwrap();
        writeln!(self.printer.deref_mut(), "All elems walked").unwrap();
        let mut outf = std::fs::OpenOptions::new().create(true).write(true).truncate(true).open(&self.res_p).unwrap();
        let doc_alloc = pretty::BoxAllocator;
        let doc = res.as_forge(&doc_alloc);
        doc.render(100, &mut outf).unwrap();
        writeln!(self.printer.deref_mut(), "Wrote analysis result to {}", &self.res_p.canonicalize().unwrap().display()).unwrap();
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
    ty.walk().any(|generic| {
        if let ty::subst::GenericArgKind::Type(ty) = generic.unpack() {
            ty_def(&ty).and_then(DefId::as_local).map_or(false, |def| {
                tcx.hir()
                    .attrs(tcx.hir().local_def_id_to_hir_id(def))
                    .iter()
                    .any(|a| a.matches_path(auth_witness_marker))
            })
        } else {
            false
        }
    })
}

fn extract_args<'tcx>(t: &mir::Terminator<'tcx>, loc: mir::Location) -> Option<Vec<Option<mir::Place<'tcx>>>> {
    match &t.kind {
        mir::TerminatorKind::Call {args, .. } => Some(args.iter().map(|a| match a {
                mir::Operand::Move(p) | mir::Operand::Copy(p) => Some(*p),
                mir::Operand::Constant(_) => None,
            }).collect()),
        _ => None,
    }
}

pub struct Visitor<'tcx, 'p> {
    tcx: TyCtxt<'tcx>,
    marked_sinks: HashSet<HirId>,
    marked_sources: HashSet<HirId>,
    functions_to_analyze: Vec<(Ident, BodyId, &'tcx rustc_hir::FnDecl<'tcx>)>,
    printers: &'p mut Printers,
}

impl<'tcx, 'p> Visitor<'tcx, 'p> {
    fn new(tcx: TyCtxt<'tcx>, printers: &'p mut Printers) -> Self {
        Self {
            tcx,
            marked_sinks: HashSet::new(),
            marked_sources: HashSet::new(),
            functions_to_analyze: vec![],
            printers,
        }
    }

    fn is_interesting_fn(&self, ident: HirId) -> bool {
        self.tcx
            .hir()
            .attrs(ident)
            .iter()
            .any(|a| a.matches_path(&ANALYZE_MARKER))
    }

    fn run(&mut self) -> std::io::Result<ProgramDescription> {
        let tcx = self.tcx;
        tcx.hir().deep_visit_all_item_likes(self);
        //println!("{:?}\n{:?}\n{:?}", self.marked_sinks, self.marked_sources, self.functions_to_analyze);
        self.analyze()
    }

    fn analyze(&mut self) -> std::io::Result<ProgramDescription> {
        let mut targets = std::mem::replace(&mut self.functions_to_analyze, vec![]);
        let tcx = self.tcx;
        let prnt: &mut dyn Write = self.printers.deref_mut();
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
        writeln!(
            prnt,
            "Analysis begin:\n  {} targets\n  {} marked sinks\n  {} marked sources",
            targets.len(),
            sink_fn_defs.len(),
            source_fn_defs.len()
        )?;
        targets.drain(..).map(|(id, b, fd)| {
            let mut called_fns_found = 0;
            let mut source_fns_found = 0;
            let mut sink_fn_defs_found = 0;
            let local_def_id = tcx.hir().body_owner_def_id(b);
            let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, local_def_id);
            use flowistry::indexed::{impls::LocationDomain, IndexedDomain};
            let body = &body_with_facts.body;
            let loc_dom = LocationDomain::new(body);
            writeln!(prnt, "{}", id.as_str())?;
            let mut source_locs = body
                .args_iter()
                .enumerate()
                .filter_map(|(i, l)| {
                    let ty = &body.local_decls[l].ty;
                    if type_has_ann(tcx, &AUTH_WITNESS_MARKER, ty) ||
                    type_has_ann(tcx, &SENSITIVE_MARKER, ty) {
                        Some((*loc_dom.value(loc_dom.arg_to_location(l)), format!("arg_{}", i)))
                    } else {
                        None
                    }
                })
                .collect::<HashMap<_, _>>();
            let source_args_found = source_locs.len();
            let flow = infoflow::compute_flow(tcx, b, body_with_facts);
            let mut flows = DfGraph::empty();
            for (bb, bbdat) in body.basic_blocks().iter_enumerated() {
                let loc = body.terminator_loc(bb);
                if let Some((t, p)) = bbdat
                    .terminator
                    .as_ref()
                    .and_then(|t| called_fn(t).map(|p| (t, p)))
                {
                    called_fns_found += 1;
                    if source_fn_defs.contains(&p) {
                        source_fns_found += 1;
                        source_locs.insert(loc, format!("call_{}", tcx.item_name(p).to_string()));
                    }
                    if sink_fn_defs.contains(&p) {
                        let ordered_mentioned_places = extract_args(t, loc).expect("Not a function call");
                        let mentioned_places = ordered_mentioned_places.iter().filter_map(|a| *a).collect::<HashSet<_>>();
                        sink_fn_defs_found += 1;
                        let matrix = flow.state_at(loc);
                        let mut terminator_printed = false;
                        for r in mentioned_places.iter() {
                            let deps = matrix.row(*r);
                            let mut header_printed = false;
                            for loc in deps.filter(|l| source_locs.contains_key(l)) {
                                if !terminator_printed {
                                    writeln!(prnt, "  {:?}", t.kind)?;
                                    terminator_printed = true;
                                }
                                if !header_printed {
                                    write!(prnt, "    {:?}:", r)?;
                                    header_printed = true
                                };
                                flows.add(
                                    &Identifier(source_locs[loc].clone()), 
                                    DataSink {
                                        function: Identifier(tcx.item_name(p).to_string()),
                                        arg_slot: ordered_mentioned_places.iter().enumerate().filter(|(_, e)| **e == Some(*r)).next().unwrap().0,
                                    }
                                );
                                write!(prnt, " {}", location_to_string(*loc, body))?;
                            }
                            if header_printed {
                                writeln!(prnt, "")?;
                            }
                        }
                    }
                };
            }
            writeln!(prnt, "Function {}:\n  {} called functions found\n  {} source args found\n  {} source fns matched\n  {} sink fns matched", id, called_fns_found, source_args_found, source_fns_found, sink_fn_defs_found)?;
            Ok((Identifier(id.as_str().to_string()), flows))
        }).collect::<std::io::Result<HashMap<Endpoint,DfGraph>>>().map(|d| ProgramDescription { d })
    }
}

impl<'tcx, 'p> intravisit::Visitor<'tcx> for Visitor<'tcx, 'p> {
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
            .any(|a| a.matches_path(&SINK_MARKER))
        {
            self.marked_sinks.insert(id);
        }
        if self
            .tcx
            .hir()
            .attrs(id)
            .iter()
            .any(|a| a.matches_path(&SOURCE_MARKER))
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
        rustc_driver::RunCompiler::new(&compiler_args, &mut Callbacks{printer, res_p}).run()
    }
}
