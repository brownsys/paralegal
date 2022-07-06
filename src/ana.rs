use std::borrow::Cow;
use std::io::Write;
use std::ops::DerefMut;

use crate::desc::*;
use crate::rust::*;
use crate::{HashMap, HashSet, Printers};

use hir::{
    def_id::DefId,
    hir_id::HirId,
    intravisit::{self, FnKind},
    BodyId,
};
use rustc_middle::{
    hir::nested_filter::OnlyBodies,
    ty::{self, TyCtxt},
};
use rustc_span::{symbol::Ident, Span, Symbol};

use flowistry::{
    infoflow,
    mir::{borrowck_facts, utils::location_to_string},
};

pub type AttrMatchT = Vec<Symbol>;

trait MetaItemMatch {
    fn match_extract<A, F: Fn(&ast::MacArgs) -> A>(&self, p: &[Symbol], f: F) -> Option<A>;
    fn matches_path(&self, p: &[Symbol]) -> bool {
        self.match_extract(p, |_| ()).is_some()
    }
}

impl MetaItemMatch for ast::Attribute {
    fn match_extract<A, F: Fn(&ast::MacArgs) -> A>(&self, p: &[Symbol], f: F) -> Option<A> {
        match &self.kind {
            rustc_ast::ast::AttrKind::Normal(ast::AttrItem { path, args, .. }, _)
                if path.segments.len() == p.len()
                    && path
                        .segments
                        .iter()
                        .zip(p)
                        .all(|(seg, i)| seg.ident.name == *i) =>
            {
                Some(f(args))
            }
            _ => None,
        }
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

fn type_ann_extract<A, F: Fn(&rustc_ast::MacArgs) -> A>(
    tcx: TyCtxt,
    ann_marker: &AttrMatchT,
    f: F,
    ty: &ty::Ty,
) -> Vec<(HirId, Vec<A>)> {
    ty.walk()
        .filter_map(|generic| {
            if let ty::subst::GenericArgKind::Type(ty) = generic.unpack() {
                ty_def(&ty).and_then(DefId::as_local).map_or(None, |def| {
                    let hid = tcx.hir().local_def_id_to_hir_id(def);
                    let anns = tcx
                        .hir()
                        .attrs(hid)
                        .iter()
                        .filter_map(|a| a.match_extract(ann_marker, &f))
                        .collect::<Vec<_>>();
                    if anns.is_empty() {
                        None
                    } else {
                        Some((hid, anns))
                    }
                })
            } else {
                None
            }
        })
        .collect()
}

fn type_descriptor_from_type<'tcx>(ty: ty::Ty<'tcx>) -> TypeDescriptor {
    Symbol::intern(&format!("{ty}").replace(":", "_"))
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

fn extract_args<'tcx>(
    t: &mir::Terminator<'tcx>,
    _loc: mir::Location,
) -> Option<Vec<Option<mir::Place<'tcx>>>> {
    match &t.kind {
        mir::TerminatorKind::Call { args, .. } => Some(
            args.iter()
                .map(|a| match a {
                    mir::Operand::Move(p) | mir::Operand::Copy(p) => Some(*p),
                    mir::Operand::Constant(_) => None,
                })
                .collect(),
        ),
        _ => None,
    }
}

pub struct Visitor<'tcx, 'p> {
    tcx: TyCtxt<'tcx>,
    marked_objects: HashMap<HirId, Vec<Annotation>>,
    functions_to_analyze: Vec<(Ident, BodyId, &'tcx rustc_hir::FnDecl<'tcx>)>,
    printers: &'p mut Printers,
}

impl<'tcx, 'p> Visitor<'tcx, 'p> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, printers: &'p mut Printers) -> Self {
        Self {
            tcx,
            marked_objects: HashMap::new(),
            functions_to_analyze: vec![],
            printers,
        }
    }

    fn should_analyze_function(&self, ident: HirId) -> bool {
        self.tcx
            .hir()
            .attrs(ident)
            .iter()
            .any(|a| a.matches_path(&crate::ANALYZE_MARKER))
    }

    pub fn run(mut self) -> std::io::Result<ProgramDescription> {
        let tcx = self.tcx;
        tcx.hir().deep_visit_all_item_likes(&mut self);
        //println!("{:?}\n{:?}\n{:?}", self.marked_sinks, self.marked_sources, self.functions_to_analyze);
        self.analyze()
    }

    fn analyze(mut self) -> std::io::Result<ProgramDescription> {
        let mut targets = std::mem::replace(&mut self.functions_to_analyze, vec![]);
        let tcx = self.tcx;
        let prnt: &mut dyn Write = self.printers.deref_mut();
        let interesting_fn_defs = self
            .marked_objects
            .keys()
            .map(|s| tcx.hir().local_def_id(*s).to_def_id())
            .collect::<HashSet<_>>();
        writeln!(
            prnt,
            "Analysis begin:\n  {} targets\n  {} marked objects",
            targets.len(),
            interesting_fn_defs.len(),
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
            let (mut source_locs, types): (HashMap<_, DataSource>, CtrlTypes) = body
                .args_iter()
                .enumerate()
                .filter_map(|(i, l)| {
                    let ty = &body.local_decls[l].ty;
                    let ty_anns = type_ann_extract(tcx, &crate::LABEL_MARKER, crate::ann_parse::ann_match_fn, ty);
                    if !ty_anns.is_empty() {
                        
                        self.marked_objects.extend(ty_anns);
                        Some((
                            (*loc_dom.value(loc_dom.arg_to_location(l)), DataSource::Argument(i)),
                            (i, type_descriptor_from_type(*ty))
                        ))
                    } else {
                        None
                    }
                })
                .unzip();
            let mut flows = Ctrl::with_input_types(types);
            let source_args_found = source_locs.len();
            let flow = infoflow::compute_flow(tcx, b, body_with_facts);
            for (bb, bbdat) in body.basic_blocks().iter_enumerated() {
                let loc = body.terminator_loc(bb);
                if let Some((t, p)) = bbdat
                    .terminator
                    .as_ref()
                    .and_then(|t| called_fn(t).map(|p| (t, p)))
                {
                    called_fns_found += 1;
                    if interesting_fn_defs.contains(&p) {
                        source_fns_found += 1;
                        source_locs.insert(loc, DataSource::FunctionCall(Identifier::new(tcx.item_name(p))));
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
                                    Cow::Borrowed(&source_locs[loc]),
                                    DataSink {
                                        function: Identifier::new(tcx.item_name(p)),
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
            Ok((Identifier::new(id.name), flows))
        }).collect::<std::io::Result<HashMap<Endpoint,Ctrl>>>().map(|controllers| ProgramDescription { controllers, annotations: self.marked_objects.into_iter().map(|(k, v)| (Identifier::new(tcx.item_name( tcx.hir().local_def_id(k).to_def_id())), (v, 
                            tcx
                            .hir()
                            .fn_decl_by_hir_id(k)
                            .map(|f| f.inputs.len())
        ))).collect() })
    }
}

impl<'tcx, 'p> intravisit::Visitor<'tcx> for Visitor<'tcx, 'p> {
    type NestedFilter = OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_id(&mut self, id: HirId) {
        let mut sink_matches = self
            .tcx
            .hir()
            .attrs(id)
            .iter()
            .filter_map(|a| a.match_extract(&crate::LABEL_MARKER, crate::ann_parse::ann_match_fn))
            .collect::<Vec<_>>();
        if !sink_matches.is_empty() {
            self.marked_objects.insert(id, sink_matches);
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
                if self.should_analyze_function(id) =>
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
