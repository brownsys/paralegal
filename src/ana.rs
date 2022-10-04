use std::borrow::Cow;

use crate::{desc::*, rust::*, sah::HashVerifications, HashMap, HashSet};

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

fn fn_defid_and_args<'tcx>(
    t: &mir::Terminator<'tcx>,
) -> Option<(DefId, Vec<Option<mir::Place<'tcx>>>)> {
    match &t.kind {
        mir::TerminatorKind::Call { func, args, .. } => {
            let fn_id = func
                .constant()
                .ok_or("Not a constant")
                .and_then(|c| match c {
                    mir::Constant {
                        literal: mir::ConstantKind::Val(_, ty),
                        ..
                    } => match ty.kind() {
                        ty::FnDef(defid, _) | ty::Closure(defid, _) => Ok(*defid),
                        _ => Err("Not function type"),
                    },
                    _ => Err("Not value level constant"),
                });
            match fn_id {
                Err(e) => {
                    error!("Could not extract root function from {func:?}. Reason: {e}");
                    None
                }
                Ok(defid) => Some((
                    defid,
                    args.iter()
                        .map(|a| match a {
                            mir::Operand::Move(p) | mir::Operand::Copy(p) => Some(*p),
                            mir::Operand::Constant(_) => None,
                        })
                        .collect(),
                )),
            }
        }
        _ => None,
    }
}

/// A struct that can be used to apply a `FnMut` to every `Place` in a MIR
/// object via the visit::Visitor` trait. Usually used to accumulate information
/// about the places.
pub struct PlaceVisitor<F>(pub F);

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

/// This function deals with the fact that flowistry uses special locations to
/// refer to function arguments. Those locations are not recognized the rustc
/// functions that operate on MIR and thus need to be filtered before doing
/// things such as indexing into a `mir::Body`.
pub fn is_real_location(body: &mir::Body, l: mir::Location) -> bool {
    body.basic_blocks().get(l.block).map(|bb| 
            // Its `<=` because if len == statement_index it refers to the
            // terminator
            // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.Location.html
            l.statement_index <= bb.statements.len())
        == Some(true)
}

pub struct Visitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    opts: &'static crate::Args,
    marked_objects: HashMap<HirId, (Vec<Annotation>, ObjectType)>,
    marked_stmts: HashMap<HirId, ((Vec<Annotation>, usize), Span, DefId)>,
    functions_to_analyze: Vec<(Ident, BodyId, &'tcx rustc_hir::FnDecl<'tcx>)>,
}

type CallSiteAnnotations = HashMap<DefId, (Vec<Annotation>, usize)>;

impl<'tcx> Visitor<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, opts: &'static crate::Args) -> Self {
        Self {
            tcx,
            opts,
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

    /// Handles a single target function
    fn handle_target(
        &self,
        hash_verifications: &mut HashVerifications,
        call_site_annotations: &mut CallSiteAnnotations,
        interesting_fn_defs: &HashMap<DefId, (Vec<Annotation>, usize)>,
        id: Ident,
        b: BodyId,
    ) -> std::io::Result<(Endpoint, Ctrl)> {
        fn register_call_site<'tcx>(
            tcx: TyCtxt<'tcx>,
            map: &mut CallSiteAnnotations,
            did: DefId,
            ann: Option<&[Annotation]>,
        ) {
            // This is a bit ugly. This basically just cleans up the fact that
            // when we integrate an annotation on a call, its slightly
            // cumbersome to find out how many arguments the call has. So I just
            // fill in the largest annotated value and then have it merge here
            // later in case we know of more arguments.
            map.entry(did)
                .and_modify(|e| {
                    e.0.extend(ann.iter().flat_map(|a| a.iter()).cloned());
                })
                .or_insert_with(|| {
                    (
                        ann.iter().flat_map(|a| a.iter()).cloned().collect(),
                        tcx.fn_sig(did).skip_binder().inputs().len(),
                    )
                });
        }

        let tcx = self.tcx;
        let local_def_id = tcx.hir().body_owner_def_id(b);
        let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, local_def_id);
        let body = &body_with_facts.body;
        let loc_dom = LocationDomain::new(body);
        let (mut source_locs, types): (HashMap<_, DataSource>, CtrlTypes) = body
            .args_iter()
            .enumerate()
            .map(|(i, l)| {
                let ty = body.local_decls[l].ty;
                let subtypes = self.annotated_subtypes(ty);
                (
                    (
                        *loc_dom.value(loc_dom.arg_to_location(l)),
                        DataSource::Argument(i),
                    ),
                    (DataSource::Argument(i), subtypes),
                )
            })
            .unzip();
        let mut flows = Ctrl::with_input_types(types);
        let flow = infoflow::compute_flow(tcx, b, body_with_facts);
        for (bb, t, p, args) in body
            .basic_blocks()
            .iter_enumerated()
            .filter_map(|(bb, bbdat)| {
                let t = bbdat.terminator();
                fn_defid_and_args(t).map(|(did, args)| (bb, t, did, args))
            })
        {
            let loc = body.terminator_loc(bb);
            let matrix = flow.state_at(loc);

            if self.opts.dump_flowistry_matrix {
                info!("Flowistry matrix for {:?}", loc);
                crate::dbg::print_flowistry_matrix(&mut std::io::stdout(), matrix).unwrap();
            }

            let anns = interesting_fn_defs.get(&p).map(|a| a.0.as_slice());
            if anns.iter().flat_map(|a| a.iter()).filter_map(Annotation::as_label_ann).any(|a| a.label == Symbol::intern("graph_dump")) {
                let non_t_g = make_non_transitive_graph(&flow, loc, body, |l| is_real_location(body, l) && body.stmt_at(l).is_right());
                crate::dbg::non_transitive_graph_as_dot(
                    &mut std::fs::OpenOptions::new().truncate(true).create(true).write(true).open("non-trans-graph.gv").unwrap(),
                    body,
                    &non_t_g,
                ).unwrap();
            }
            let stmt_anns = self.statement_anns_by_loc(p, t);
            let bound_sig = tcx.fn_sig(p);
            let is_safe = is_safe_function(&bound_sig);
            let interesting_output_types: HashSet<_> =
                self.annotated_subtypes(bound_sig.skip_binder().output());

            if is_safe
                && anns.is_none()
                && interesting_output_types.is_empty()
                && stmt_anns.is_none()
            {
                continue;
            }

            let mentioned_places = args.iter().filter_map(|a| *a).collect::<HashSet<_>>();

            let src_desc = DataSource::FunctionCall(identifier_for_fn(tcx, p));
            source_locs.insert(loc, src_desc.clone());
            if !interesting_output_types.is_empty() {
                flows.types.insert(src_desc, interesting_output_types);
            }

            for r in mentioned_places.iter() {
                let deps = matrix.row(*r);
                for loc in deps.filter(|l| source_locs.contains_key(l)) {
                    flows.add(
                        Cow::Borrowed(&source_locs[loc]),
                        DataSink {
                            function: Identifier::new(tcx.item_name(p)),
                            arg_slot: args
                                .iter()
                                .enumerate()
                                .find(|(_, e)| **e == Some(*r))
                                .unwrap()
                                .0,
                        },
                    );
                }
            }
            register_call_site(tcx, call_site_annotations, p, anns);
            if let Some(anns) = stmt_anns {
                for ann in anns.iter().filter_map(Annotation::as_exception_annotation) {
                    hash_verifications.handle(ann, tcx, t, body, loc, matrix);
                }
                // TODO this is attaching to functions instead of call
                // sites. Once we start actually tracking call sites
                // this needs to be adjusted
                register_call_site(tcx, call_site_annotations, p, Some(anns));
            }
        }
        Ok((Identifier::new(id.name), flows))
    }

    /// Main analysis driver
    fn analyze(mut self) -> std::io::Result<ProgramDescription> {
        let tcx = self.tcx;
        let mut targets = std::mem::replace(&mut self.functions_to_analyze, vec![]);
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
        let mut call_site_annotations: CallSiteAnnotations = HashMap::new();
        crate::sah::HashVerifications::with(|hash_verifications| {
            targets
                .drain(..)
                .map(|(id, b, _)| {
                    self.handle_target(
                        hash_verifications,
                        &mut call_site_annotations,
                        &interesting_fn_defs,
                        id,
                        b,
                    )
                })
                .collect::<std::io::Result<HashMap<Endpoint, Ctrl>>>()
                .map(|controllers| ProgramDescription {
                    controllers,
                    annotations: call_site_annotations
                        .into_iter()
                        .map(|(k, v)| (identifier_for_fn(tcx, k), (v.0, ObjectType::Function(v.1))))
                        .chain(
                            self.marked_objects
                                .iter()
                                .filter(|kv| kv.1 .1 == ObjectType::Type)
                                .map(|(k, v)| (identifier_for_hid(tcx, *k), v.clone())),
                        )
                        .collect(),
                })
        })
    }

    /// XXX: This selector is somewhat problematic. For one it matches via
    /// source locations, rather than id, and for another we're using `find`
    /// here, which would discard additional matching annotations.
    fn statement_anns_by_loc(&self, p: DefId, t: &mir::Terminator<'tcx>) -> Option<&[Annotation]> {
        self.marked_stmts
            .iter()
            .find(|(_, (_, s, f))| p == *f && s.contains(t.source_info.span))
            .map(|t| t.1 .0 .0.as_slice())
    }
}

fn extract_places<'tcx>(l: mir::Location, body: &mir::Body<'tcx>) -> HashSet<mir::Place<'tcx>> {
    let mut places = HashSet::new();
    let mut vis = PlaceVisitor(|p: &mir::Place<'tcx>| { places.insert(*p); });
    body.basic_blocks()[l.block].visitable(l.statement_index).apply(l, &mut vis);
    places
}

use flowistry::indexed::{IndexMatrix, IndexSet};

pub type NonTransitiveGraph<'tcx> = HashMap<mir::Location, IndexMatrix<mir::Place<'tcx>, mir::Location>>;

fn make_non_transitive_graph<'a, 'tcx, P: FnMut(mir::Location) -> bool>(flow_results: &flowistry::infoflow::FlowResults<'a, 'tcx>, start_from: mir::Location, body: &mir::Body<'tcx>, mut dependency_selector: P) -> NonTransitiveGraph<'tcx> {
    let loc_dom = flow_results.analysis.location_domain();
    let loc_deps = loc_dom.as_vec().iter().filter(|l| is_real_location(body, **l)).map(|l| {
        let places = extract_places(*l, body);
        let my_flow = flow_results.state_at(*l);
        let deps = places.iter().map(|p| my_flow.row_set(*p)).fold(IndexSet::new(&flow_results.analysis.location_domain()), |mut agg, s| { agg.union(&s); agg });
        (l, (places, deps))
    }).collect::<HashMap<_,_>>();
    let mut queue = vec![start_from];

    let mut graph = HashMap::new();
    let mut dependency_mask = IndexSet::new(loc_dom);
    for i in loc_dom.as_vec().iter() {
        if !dependency_selector(*i) {
            dependency_mask.insert(i);
        }
    }

    while let Some(n) = queue.pop() {
        let mut matrix = IndexMatrix::new(loc_dom);
        if graph.contains_key(&n) {
            continue;
        } 
        let f = flow_results.state_at(n);
        let mut mask_and_self = dependency_mask.clone();
        mask_and_self.insert(n);
        let (places, _) = &loc_deps[&n];
        for p in places {
            let mut deps = f.row_set(*p).to_owned();
            deps.subtract(&mask_and_self);
            deps.iter().for_each(|l| {
                if let Some((_, ldeps)) = loc_deps.get(l) {
                    if !deps.iter().any(|l2| l2 != l && loc_deps.get(l2).map_or(false, |d| d.1.is_superset(&ldeps))) {
                        queue.push(*l);
                        matrix.insert(*p, l);
                    }
                }
            })
        }
        graph.insert(n, matrix);
    }
    graph
}

fn is_safe_function<'tcx>(bound_sig: &ty::Binder<'tcx, ty::FnSig<'tcx>>) -> bool {
    return false;
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
            Annotation::Label(LabelAnnotation { refinement, .. }) => {
                Box::new(refinement.on_argument().iter()) as Box<dyn Iterator<Item = &u16>>
            }
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

    /// Checks for annotations on this id and collects all those id's that have
    /// been annotated.
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

    /// Finds the functions that have been marked as targets.
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
