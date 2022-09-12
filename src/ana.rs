extern crate either;

use std::borrow::Cow;

use crate::desc::*;
use crate::rust::*;
use crate::{HashMap, HashSet};
use either::Either;

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
    indexed::{impls::LocationDomain, IndexedDomain},
    infoflow,
    mir::borrowck_facts,
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

fn ty_def(ty: ty::Ty) -> Option<DefId> {
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

fn generic_arg_as_type(a: ty::subst::GenericArg) -> Option<ty::Ty> {
    match a.unpack() {
        ty::subst::GenericArgKind::Type(t) => Some(t),
        _ => None,
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

/// A struct that can be used to apply a `FnMut` to every `Place` in a MIR
/// object via the visit::Visitor` trait. Usually used to accumulate information
/// about the places.
struct PlaceVisitor<F>(F);

impl<'tcx, F: FnMut(&mir::Place<'tcx>)> mir::visit::Visitor<'tcx> for PlaceVisitor<F> {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) {
        self.0(place)
    }
}

/// A struct that can be used to apply a `FnMut` to every `Place` in a MIR
/// object via the `visit::MutVisitor` trait. Crucial difference to
/// `PlaceVisitor` is that this function can alter the place itself.
struct RePlacer<'tcx, F>(TyCtxt<'tcx>, F);


impl<'tcx, F: FnMut(&mut mir::Place<'tcx>)> mir::visit::MutVisitor<'tcx> for RePlacer<'tcx, F> {
    fn tcx<'a>(&'a self) -> TyCtxt<'tcx> {
        self.0
    }
    fn visit_place(
        &mut self,
        place: &mut mir::Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) {
        self.1(place)
    }
}

/// This function deals with the fact that flowistry uses special locations to
/// refer to function arguments. Those locations are not recognized the rustc
/// functions that operate on MIR and thus need to be filtered before doing
/// things such as indexing into a `mir::Body`.
fn is_real_location(loc_dom: &LocationDomain, body: &mir::Body, l: mir::Location) -> bool {
    body.basic_blocks()
        .get(l.block)
        .map(|bb| 
            // Its `<=` because if len == statement_index it refers to the
            // terminator
            // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.Location.html
            bb.statements.len() <= l.statement_index)
        == Some(true)
}

fn compute_verification_hash_for_stmt<'tcx>(
    tcx: TyCtxt<'tcx>,
    t: &mir::Terminator<'tcx>,
    loc: mir::Location,
    body: &mir::Body<'tcx>,
    loc_dom: &LocationDomain,
    matrix: &<flowistry::infoflow::FlowAnalysis<'_, 'tcx> as rustc_mir_dataflow::AnalysisDomain<
        'tcx,
    >>::Domain,
) -> VerificationHash {
    use mir::visit::Visitor;
    use rustc_data_structures::stable_hasher::{HashStable, StableHasher};
    let mut hasher = StableHasher::new();
    tcx.create_stable_hashing_context().while_hashing_spans(false, |mut hctx|{

        t.kind.hash_stable(&mut hctx, &mut hasher);
        {
            use mir::visit::MutVisitor;
            let mut loc_set = HashSet::<mir::Location>::new();
            let mut vis = PlaceVisitor(|pl: &mir::Place<'tcx>| {
                loc_set.extend(matrix.row(*pl).filter(|l| is_real_location(loc_dom, body, **l)));
            });

            vis.visit_terminator(t, loc);
            let mut replacer = RePlacer(tcx, {
                let mut re_local_er = HashMap::new();
                let mut new_local_er = mir::Local::from_usize(0);
                move |place : &mut mir::Place| {
                    place.local = *re_local_er.entry(place.local).or_insert_with(|| {
                        let new = new_local_er;
                        new_local_er = new_local_er + 1;
                        new
                    })
                }
            });

            // This computation does two things at one. It takes all basic
            // blocks, creating a slice over each with respect to the program
            // location of interest. Then it immediately hashes all interesting
            // locations. As a result it never needs to materialize the actual
            // slice but only its hash.
            //
            // Read the Notion to know more about this https://www.notion.so/justus-adam/Attestation-Hash-shouldn-t-change-if-unrelated-statements-change-19f4b036d85643b4ae6a9b8358e3cb70#7c35960849524580b720d3207c70004f
            body.basic_blocks().iter_enumerated().for_each(|(bbidx, bbdat)| {
                let termidx = bbdat.statements.len();
                bbdat.statements.iter().enumerate().for_each(|(stmtidx, stmt)| {
                    let loc = mir::Location {block: bbidx, statement_index: stmtidx};
                    if loc_set.contains(&loc) {
                        let mut new_stmt = stmt.clone();
                        replacer.visit_statement(&mut new_stmt, loc);
                        new_stmt.hash_stable(&mut hctx, &mut hasher);
                    }
                });
                let termloc = mir::Location {block: bbidx, statement_index: termidx};
                if loc_set.contains(&termloc) {
                    let mut new_term = bbdat.terminator().clone();
                    replacer.visit_terminator(&mut new_term, termloc);
                    new_term.hash_stable(&mut hctx, &mut hasher);
                }
            });

        }
    });
    hasher.finish()
}

pub struct Visitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    marked_objects: HashMap<HirId, (Vec<Annotation>, ObjectType)>,
    marked_stmts: HashMap<HirId, ((Vec<Annotation>, usize), Span, DefId)>,
    functions_to_analyze: Vec<(Ident, BodyId, &'tcx rustc_hir::FnDecl<'tcx>)>,
}

impl<'tcx> Visitor<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            marked_objects: HashMap::new(),
            marked_stmts: HashMap::new(),
            functions_to_analyze: vec![],
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

    fn annotated_subtypes(&self, ty: ty::Ty) -> HashSet<TypeDescriptor> {
        ty.walk()
            .filter_map(|ty| {
                generic_arg_as_type(ty)
                    .and_then(ty_def)
                    .and_then(DefId::as_local)
                    .and_then(|def| {
                        let hid = self.tcx.hir().local_def_id_to_hir_id(def);
                        if self.marked_objects.contains_key(&hid) {
                            Some(Identifier::new(
                                self.tcx
                                    .item_name(self.tcx.hir().local_def_id(hid).to_def_id()),
                            ))
                        } else {
                            None
                        }
                    })
            })
            .collect()
    }

    fn analyze(mut self) -> std::io::Result<ProgramDescription> {
        let mut targets = std::mem::replace(&mut self.functions_to_analyze, vec![]);
        let tcx = self.tcx;
        let interesting_fn_defs = self
            .marked_objects
            .iter()
            .filter_map(|(s, v)| match v.1 {
                ObjectType::Function(i) => {
                    Some((tcx.hir().local_def_id(*s).to_def_id(), (v.0.clone(), i)))
                }
                _ => None,
            })
            .collect::<HashMap<_, _>>();
        info!(
            "Analysis begin:\n  {} targets\n  {} marked objects",
            targets.len(),
            interesting_fn_defs.len(),
        );
        type CallSiteAnnotations = HashMap<DefId, (Vec<Annotation>, usize)>;
        let mut call_site_annotations: CallSiteAnnotations = HashMap::new();
        fn register_call_site(
            map: &mut CallSiteAnnotations,
            did: DefId,
            ann: &(Vec<Annotation>, usize),
        ) {
            // This is a bit ugly. This basically just cleans up the fact that
            // when we integrate an annotation on a call, its slightly
            // cumbersome to find out how many arguments the call has. So I just
            // fill in the largest annotated value and then have it merge here
            // later in case we know of more arguments.
            map.entry(did)
                .and_modify(|e| {
                    e.0.extend(ann.0.iter().cloned());
                    e.1 = ann.1.max(e.1);
                })
                .or_insert_with(|| ann.clone());
        }
        let mut unsuccessful_hash_verifications = 0;
        let res = targets.drain(..).map(|(id, b, _)| {
            let mut called_fns_found = 0;
            let mut source_fns_found = 0;
            let mut sink_fn_defs_found = 0;
            let local_def_id = tcx.hir().body_owner_def_id(b);
            let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, local_def_id);
            let body = &body_with_facts.body;
            let loc_dom = LocationDomain::new(body);
            info!("{}", id.as_str());
            let (mut source_locs, types): (HashMap<_, DataSource>, CtrlTypes) = body
                .args_iter()
                .enumerate()
                .filter_map(|(i, l)| {
                    let ty = body.local_decls[l].ty;
                    let subtypes = self.annotated_subtypes(ty);
                    if !subtypes.is_empty() {
                        Some((
                            (*loc_dom.value(loc_dom.arg_to_location(l)), DataSource::Argument(i)),
                            (DataSource::Argument(i), subtypes)
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
                    if let Some(ann) = interesting_fn_defs.get(&p) {
                        register_call_site(&mut call_site_annotations, p, ann);
                        source_fns_found += 1;
                        let src_desc = DataSource::FunctionCall(identifier_for_fn(tcx, p));
                        source_locs.insert(loc, src_desc.clone());
                        let interesting_output_types : HashSet<_> = self.annotated_subtypes(tcx.fn_sig(p).skip_binder().output());
                        if !interesting_output_types.is_empty() {
                            flows.types.insert(src_desc, interesting_output_types);
                        }
                        let ordered_mentioned_places = extract_args(t, loc).expect("Not a function call");
                        let mentioned_places = ordered_mentioned_places.iter().filter_map(|a| *a).collect::<HashSet<_>>();
                        sink_fn_defs_found += 1;
                        let matrix = flow.state_at(loc);
                        for r in mentioned_places.iter() {
                            let deps = matrix.row(*r);
                            for loc in deps.filter(|l| source_locs.contains_key(l)) {
                                flows.add(
                                    Cow::Borrowed(&source_locs[loc]),
                                    DataSink {
                                        function: Identifier::new(tcx.item_name(p)),
                                        arg_slot: ordered_mentioned_places.iter().enumerate().filter(|(_, e)| **e == Some(*r)).next().unwrap().0,
                                    }
                                );
                            }
                        }
                    }
                    if let Some((_, (ann, _, _))) = self.marked_stmts.iter().find(|(_, (_, s, f))| p == *f && s.contains(t.source_info.span)) {

                        let matrix = flow.state_at(loc);
                        for ann in ann.0.iter().filter_map(Annotation::as_exception_annotation) {
                            let hash = compute_verification_hash_for_stmt(tcx, t, loc, body, &loc_dom, matrix);
                            if let Some(old_hash) = ann.verification_hash {
                                if hash != old_hash {
                                    unsuccessful_hash_verifications += 1;
                                    println!("Verification hash checking failed for exception annotation. Please review the code and then paste in the updated hash \"{hash:032x}\"");
                                }
                            } else {
                                unsuccessful_hash_verifications += 1;
                                println!("Exception annotation is missing a verification hash. Please submit this code for review and once approved add `verification_hash = \"{hash:032x}\"` into the annotation.");
                            }
                        }
                        // TODO this is attaching to functions instead of call
                        // sites. Once we start actually tracking call sites
                        // this needs to be adjusted
                        register_call_site(&mut call_site_annotations, p, ann);
                    }
                };
            }
            info!("Function {}:\n  {} called functions found\n  {} source args found\n  {} source fns matched\n  {} sink fns matched", id, called_fns_found, source_args_found, source_fns_found, sink_fn_defs_found);
            Ok((Identifier::new(id.name), flows))
        }).collect::<std::io::Result<HashMap<Endpoint,Ctrl>>>().map(|controllers| ProgramDescription { controllers, annotations: call_site_annotations.into_iter().map(|(k, v)| (identifier_for_fn(tcx, k), (v.0, ObjectType::Function(v.1)))
        ).chain(self.marked_objects.iter().filter(|kv| kv.1.1 == ObjectType::Type).map(|(k, v)| (identifier_for_hid(tcx, *k), v.clone()))).collect() });
        assert_eq!(unsuccessful_hash_verifications, 0, "{unsuccessful_hash_verifications} verification hashes were not present or invalid. Please review, update and rerun.");
        return res;
    }
}

fn identifier_for_hid<'tcx>(tcx: TyCtxt<'tcx>, hid: HirId) -> Identifier {
    Identifier::new(tcx.item_name(tcx.hir().local_def_id(hid).to_def_id()))
}

fn identifier_for_fn<'tcx>(tcx: TyCtxt<'tcx>, p: DefId) -> Identifier {
    Identifier::new(tcx.item_name(p))
}

fn obj_type_for_stmt_ann(anns: &[Annotation]) -> usize {
    *anns
        .iter()
        .flat_map(|a| match a {
            Annotation::Label(LabelAnnotation {
                refinement: AnnotationRefinement::Argument(nums),
                ..
            }) => Box::new(nums.iter()) as Box<dyn Iterator<Item = &u16>>,
            Annotation::Exception(_) => Box::new(std::iter::once(&0)),
            _ => panic!("Unsupported annotation type for statement annotation"),
        })
        .max()
        .unwrap() as usize
}

impl<'tcx> intravisit::Visitor<'tcx> for Visitor<'tcx> {
    type NestedFilter = OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_id(&mut self, id: HirId) {
        let tcx = self.tcx;
        let hir = self.tcx.hir();
        let sink_matches = hir
            .attrs(id)
            .iter()
            .filter_map(|a| {
                a.match_extract(&crate::LABEL_MARKER, |i| {
                    Annotation::Label(crate::ann_parse::ann_match_fn(i))
                })
                .or_else(|| {
                    a.match_extract(&crate::OTYPE_MARKER, |i| {
                        Annotation::OType(crate::ann_parse::otype_ann_match(i))
                    })
                })
                .or_else(|| {
                    a.match_extract(&crate::EXCEPTION_MARKER, |i| {
                        Annotation::Exception(crate::ann_parse::match_exception(i))
                    })
                })
            })
            .collect::<Vec<_>>();
        if !sink_matches.is_empty() {
            let node = self.tcx.hir().find(id).unwrap();
            assert!(if let Some(decl) = node.fn_decl() {
                self.marked_objects
                    .insert(id, (sink_matches, ObjectType::Function(decl.inputs.len())))
                    .is_none()
            } else {
                match node {
                    hir::Node::Ty(_)
                    | hir::Node::Item(hir::Item {
                        kind: hir::ItemKind::Struct(..),
                        ..
                    }) => self
                        .marked_objects
                        .insert(id, (sink_matches, ObjectType::Type))
                        .is_none(),
                    _ => {
                        let e = match node {
                            hir::Node::Expr(e) => e,
                            hir::Node::Stmt(hir::Stmt { kind, .. }) => match kind {
                                hir::StmtKind::Expr(e) | hir::StmtKind::Semi(e) => e,
                                _ => panic!("Unsupported statement kind"),
                            },
                            _ => panic!("Unsupported object type for annotation {node:?}"),
                        };
                        let obj_type = obj_type_for_stmt_ann(&sink_matches);
                        let did = match e.kind {
                            hir::ExprKind::MethodCall(_, _, _) => {
                                let body_id = hir.enclosing_body_owner(id);
                                let tcres = tcx.typeck(hir.local_def_id(body_id));
                                tcres.type_dependent_def_id(e.hir_id).unwrap_or_else(|| {
                                    panic!("No DefId found for method call {e:?}")
                                })
                            }
                            hir::ExprKind::Call(
                                hir::Expr {
                                    hir_id,
                                    kind: hir::ExprKind::Path(p),
                                    ..
                                },
                                _,
                            ) => {
                                let body_id = hir.enclosing_body_owner(id);
                                let tcres = tcx.typeck(hir.local_def_id(body_id));
                                match tcres.qpath_res(p, *hir_id) {
                                    hir::def::Res::Def(_, did) => did,
                                    res => panic!("Not a function? {res:?}"),
                                }
                            }
                            _ => panic!("Unsupported expression kind {:?}", e.kind),
                        };
                        self.marked_stmts
                            .insert(id, ((sink_matches, obj_type), e.span, did))
                            .is_none()
                    }
                }
            })
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
