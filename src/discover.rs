//! MIR visitor ([`CollectingVisitor`]) that discovers and stores all items of interest.
//!
//! Items of interest is anything annotated with one of the `dfpp::`
//! annotations.
use crate::{
    args::Args,
    consts,
    desc::*,
    rust::*,
    utils::{self, *},
    HashMap,
};

use hir::{
    def_id::DefId,
    hir_id::HirId,
    intravisit::{self, FnKind},
    BodyId,
};
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_span::{symbol::Ident, Span, Symbol};
use std::{cell::RefCell, rc::Rc};

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
pub type MarkedObjects = Rc<RefCell<HashMap<LocalDefId, (Vec<Annotation>, ObjectType)>>>;

/// This visitor traverses the items in the analyzed crate to discover
/// annotations and analysis targets and store them in this struct. After the
/// discovery phase [`Self::analyze`] is used to drive the
/// actual analysis. All of this is conveniently encapsulated in the
/// [`Self::run`] method.
pub struct CollectingVisitor<'tcx> {
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
    pub external_annotations: ExternalMarkers,
}

pub type ExternalMarkers = HashMap<DefId, (Vec<MarkerAnnotation>, ObjectType)>;

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

/// Given the TOML of external annotations we have parsed, resolve the paths
/// (keys of the map) to [`DefId`]s.
fn resolve_external_markers(
    opts: &Args,
    tcx: TyCtxt,
    markers: &crate::RawExternalMarkers,
) -> ExternalMarkers {
    use hir::def::Res;
    let new_map: ExternalMarkers = markers
        .into_iter()
        .filter_map(|(path, marker)| {
            let segment_vec = path.split("::").collect::<Vec<_>>();
            let res = utils::resolve::def_path_res(tcx, &segment_vec);
            let (did, typ) = match res {
                Res::Def(kind, did) => Some((
                    did,
                    if kind.is_fn_like() {
                        ObjectType::Function(
                            tcx.fn_sig(did).skip_binder().skip_binder().inputs().len(),
                        )
                    } else {
                        // XXX add an actual match here
                        ObjectType::Type
                    },
                )),
                other if opts.relaxed() => {
                    warn!("{path} did not resolve to an item ({other:?})");
                    None
                }
                other => panic!("{path} did not resolve to an item ({other:?})"),
            }?;
            Some((did, (marker.clone(), typ)))
        })
        .collect();
    assert_eq!(new_map.len(), markers.len());
    new_map
}

// fn resolve_external_markers_old(tcx: TyCtxt, markers: &crate::RawExternalMarkers) -> ExternalMarkers {
//     struct Value<'a> {
//         table: HashMap<&'a str, Value<'a>>,
//         value: Option<&'a [MarkerAnnotation]>,
//     }
//     impl<'a> Value<'a> {
//         fn get(&self, key: &str) -> Option<&Value<'a>> {
//             self.table.get(key)
//         }
//         fn new() -> Self {
//             Self {
//                 table: HashMap::new(),
//                 value: None,
//             }
//         }
//     }
//     let mut map = Value::new();

//     for (path, ann) in markers {
//         let segments = path.split("::");
//         let mut tab_ref = &mut map;
//         for segment in segments {
//             tab_ref = tab_ref.table.entry(segment).or_insert_with(Value::new);
//         }

//         assert!(tab_ref.value.replace(ann).is_none())
//     }

//     fn resolve_map_in_module<'b, 'v: 'b, 'tcx: 'b, 'r: 'b>(
//         tcx: TyCtxt<'tcx>,
//         module: DefId,
//         v: &'r Value<'v>,
//     ) -> impl Iterator<Item = (DefId, Vec<MarkerAnnotation>)> + 'b {
//         let parent = module;
//         let clone_val = |v: &[_]| v.iter().cloned().collect::<Vec<_>>();
//         v.value
//             .map(|v| (module, clone_val(v)))
//             .into_iter()
//             .chain({
//                 use hir::def::DefKind;
//                 match tcx.def_kind(module) {
//                     _ if v.table.is_empty() => Box::new(std::iter::empty()) as Box<dyn Iterator<Item = (DefId, Vec<MarkerAnnotation>)> + 'b>,
//                     DefKind::Mod =>
//                         Box::new(
//                             tcx.module_children(module)
//                                 .into_iter()
//                                 .filter_map(move |child| {
//                                     let module = match child.res {
//                                         hir::def::Res::Def(_, did) => did,
//                                         _ => unreachable!(),
//                                     };
//                                     debug!("Seeing child {} of {} (is {:?})", tcx.def_path_str(module), tcx.item_name(parent), tcx.def_kind(module));
//                                     let v = v.table.get(child.ident.as_str())?;
//                                     Some((module, v))
//                                 })
//                                 .flat_map(move |(module, v)| resolve_map_in_module(tcx, module, v)),
//                         ) as Box<_>,
//                     DefKind::Struct | DefKind::Enum => {
//                         debug!("Saw {} impls for {} ({:?})", tcx.all_impls(module).count(), tcx.item_name(module), tcx.def_kind(module));
//                         Box::new(tcx.all_impls(module)
//                             .flat_map(move |impl_| {
//                                 let items = tcx.associated_items(impl_);
//                                 debug!("Handling impl {}", tcx.item_name(impl_));
//                                 v.table.iter()
//                                     .filter_map(move |(name, val)| {
//                                         let mut it = items.filter_by_name_unhygienic(Symbol::intern(name));
//                                         let my_item = it.next()?;
//                                         assert!(it.next().is_none());
//                                         assert!(val.table.is_empty());
//                                         let my_val = val.value?;
//                                         Some((my_item.def_id, clone_val(my_val)))
//                                     })
//                             })) as Box<_>
//                     }
//                     other => {
//                         let name = tcx.item_name(module);
//                         warn!("Unsupported def kind {other:?} for {name}");
//                         Box::new(std::iter::empty()) as Box<_>
//                     },
//                 }
//             })
//     }

//     let final_map = tcx
//         .crates(())
//         .into_iter()
//         .filter_map(|c| {
//             let name = tcx.crate_name(*c);
//             let crate_map = map.get(name.as_str())?;
//             Some((
//                 DefId {
//                     krate: *c,
//                     index: def_id::CRATE_DEF_INDEX,
//                 },
//                 crate_map,
//             ))
//         })
//         .flat_map(|(module, map)| resolve_map_in_module(tcx, module, map))
//         .collect::<ExternalMarkers>();
//     assert_eq!(final_map.len(), markers.len());
//     final_map
// }

impl<'tcx> CollectingVisitor<'tcx> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        opts: &'static crate::Args,
        external_annotations: &crate::RawExternalMarkers,
    ) -> Self {
        let external_annotations = resolve_external_markers(opts, tcx, external_annotations);
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
    fn should_analyze_function(&self, ident: LocalDefId) -> bool {
        self.tcx
            .hir()
            .attrs(self.tcx.local_def_id_to_hir_id(ident))
            .iter()
            .any(|a| a.matches_path(&consts::ANALYZE_MARKER))
    }
}

/// Confusingly named this function actually computed the highest index
/// mentioned in any `on_argument` refinement in the provided annotation slice.
fn obj_type_for_stmt_ann(anns: &[Annotation]) -> usize {
    anns.iter()
        .flat_map(|a| match a {
            Annotation::Label(MarkerAnnotation { refinement, .. }) => {
                Box::new(refinement.on_argument().into_iter_set_in_domain())
                    as Box<dyn Iterator<Item = u32>>
            }
            Annotation::Exception(_) => Box::new(std::iter::once(0)),
            _ => panic!("Unsupported annotation type for statement annotation"),
        })
        .max()
        .unwrap() as usize
}

impl<'tcx> intravisit::Visitor<'tcx> for CollectingVisitor<'tcx> {
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
                        Annotation::OType(crate::ann_parse::otype_ann_match(i, tcx))
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
                    .insert(
                        id.expect_owner().def_id,
                        (sink_matches, ObjectType::Function(decl.inputs.len())),
                    )
                    .is_none()
            } else {
                // I'm restricting the Ctor in the second set of patterns to
                // `Unit`, because in that case the annotation ends up on the
                // synthesized constructor (for some reason).
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
                        .insert(id.expect_owner().def_id, (sink_matches, ObjectType::Type))
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
                            hir::ExprKind::MethodCall(_, _, _, _) => {
                                let body_id = hir.enclosing_body_owner(id);
                                let tcres = tcx.typeck(body_id);
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
                                let tcres = tcx.typeck(body_id);
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
        _s: Span,
        id: LocalDefId,
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
        intravisit::walk_fn(self, kind, declaration, body_id, id)
    }
}
