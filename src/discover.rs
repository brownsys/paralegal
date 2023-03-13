use crate::{
    consts, dbg,
    desc::*,
    ir::*,
    rust::*,
    sah::HashVerifications,
    utils::{PlaceExt, *},
    Either, HashMap, HashSet,
};

use hir::{
    def_id::DefId,
    hir_id::HirId,
    intravisit::{self, FnKind},
    BodyId,
};
use mir::{Location, Place, Terminator, TerminatorKind};
use rustc_borrowck::BodyWithBorrowckFacts;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_span::{symbol::Ident, Span, Symbol};
use std::{borrow::Cow, cell::RefCell, rc::Rc};

use flowistry::{
    indexed::IndexSet,
    infoflow::{FlowAnalysis, FlowDomain, NonTransitiveFlowDomain},
    mir::{
        aliases::Aliases,
        borrowck_facts::{self, CachedSimplifedBodyWithFacts},
        engine::AnalysisResults,
    },
};

/// Values of this type can be matched against Rust attributes
pub type AttrMatchT = Vec<Symbol>;

/// A mapping of annotations that are attached to function calls.
///
/// XXX: This needs to be adjusted to attach to the actual call site instead of
/// the function `DefId`
pub type CallSiteAnnotations = HashMap<DefId, (Vec<Annotation>, usize)>;
/// A map of objects for which we have found annotations.
///
/// This is sharable so we can stick it into the
/// [`SkipAnnotatedFunctionSelector`]. Technically at that point this map is
/// read-only.
pub type MarkedObjects = Rc<RefCell<HashMap<HirId, (Vec<Annotation>, ObjectType)>>>;

/// This visitor traverses the items in the analyzed crate to discover
/// annotations and analysis targets and store them in this struct. After the
/// discovery phase [`Self::analyze`] is used to drive the
/// actual analysis. All of this is conveniently encapsulated in the
/// [`Self::run`] method.
pub struct CollectingVisitor<'tcx, 'a> {
    /// Reference to rust compiler queries.
    pub tcx: TyCtxt<'tcx>,
    /// Command line arguments.
    pub opts: &'static crate::Args,
    /// In this map we will be accumulating the definitions we found annotations
    /// for (except `analyze` annotations, those are in `function_to_analyze`),
    /// which annotations they are and what type of item it is.
    pub marked_objects: MarkedObjects,
    /// Expressions and statements we found annotations on. At the moment those
    /// should only be [`ExceptionAnnotation`]s.
    pub marked_stmts: HashMap<HirId, ((Vec<Annotation>, usize), Span, DefId)>,
    /// Functions that are annotated with `#[dfpp::analyze]`. For these we will
    /// later perform the analysis
    pub functions_to_analyze: Vec<FnToAnalyze>,

    /// Annotations that are to be placed on external functions and types.
    pub external_annotations: &'a AnnotationMap,
}

/// A function we will be targeting to analyze with
/// [`CollectingVisitor::handle_target`].
pub struct FnToAnalyze {
    pub name: Ident,
    pub body_id: BodyId,
}

impl FnToAnalyze {
    /// Give me a name that describes this function.
    pub fn name(&self) -> Symbol {
        self.name.name
    }
}

impl<'tcx, 'a> CollectingVisitor<'tcx, 'a> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        opts: &'static crate::Args,
        external_annotations: &'a AnnotationMap,
    ) -> Self {
        Self {
            tcx,
            opts,
            marked_objects: Rc::new(RefCell::new(HashMap::new())),
            marked_stmts: HashMap::new(),
            functions_to_analyze: vec![],
            external_annotations,
        }
    }

    /// Does the function named by this id have the `dfpp::analyze` annotation
    fn should_analyze_function(&self, ident: HirId) -> bool {
        self.tcx
            .hir()
            .attrs(ident)
            .iter()
            .any(|a| a.matches_path(&consts::ANALYZE_MARKER))
    }
}

/// Confusingly named this function actually computed the highest index
/// mentioned in any `on_argument` refinement in the provided annotation slice.
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

impl<'tcx, 'a> intravisit::Visitor<'tcx> for CollectingVisitor<'tcx, 'a> {
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
                a.match_extract(&consts::LABEL_MARKER, |i| {
                    Annotation::Label(crate::ann_parse::ann_match_fn(i))
                })
                .or_else(|| {
                    a.match_extract(&consts::OTYPE_MARKER, |i| {
                        Annotation::OType(crate::ann_parse::otype_ann_match(i))
                    })
                })
                .or_else(|| {
                    a.match_extract(&consts::EXCEPTION_MARKER, |i| {
                        Annotation::Exception(crate::ann_parse::match_exception(i))
                    })
                })
            })
            .collect::<Vec<_>>();
        if !sink_matches.is_empty() {
            let node = self.tcx.hir().find(id).unwrap();
            assert!(if let Some(decl) = node.fn_decl() {
                self.marked_objects
                    .as_ref()
                    .borrow_mut()
                    .insert(id, (sink_matches, ObjectType::Function(decl.inputs.len())))
                    .is_none()
            } else {
                // I'm restricting the Ctor here to `Unit`, because in that case
                // the annotation ends up on the synthesized constructor (for
                // some reason).
                match node {
                    hir::Node::Ty(_)
                    | hir::Node::Item(hir::Item {
                        kind: hir::ItemKind::Struct(..),
                        ..
                    })
                    | hir::Node::Ctor(hir::VariantData::Unit(..)) => self
                        .marked_objects
                        .as_ref()
                        .borrow_mut()
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
        kind: FnKind<'tcx>,
        declaration: &'tcx rustc_hir::FnDecl<'tcx>,
        body_id: BodyId,
        s: Span,
        id: HirId,
    ) {
        match &kind {
            FnKind::ItemFn(name, _, _) | FnKind::Method(name, _)
                if self.should_analyze_function(id) =>
            {
                self.functions_to_analyze.push(FnToAnalyze {
                    name: *name,
                    body_id,
                });
            }
            _ => (),
        }

        // dispatch to recursive walk. This is probably unnecessary but if in
        // the future we decide to do something with nested items we may need
        // it.
        intravisit::walk_fn(self, kind, declaration, body_id, s, id)
    }
}