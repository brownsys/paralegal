use std::str::FromStr;

use ast::Mutability;
use hir::{
    def::{self, DefKind},
    def_id::CrateNum,
    def_id::LocalDefId,
    def_id::LOCAL_CRATE,
    ImplItemRef, ItemKind, Node, PrimTy, TraitItemRef,
};
use rustc_ast::{
    self as ast,
    token::{Token, TokenKind},
    Expr, ExprKind, Path, PathSegment, QSelf, Ty, TyKind,
};
use rustc_hir::{self as hir, def_id::DefId};
use rustc_middle::{
    middle::resolve_bound_vars::ResolveBoundVars,
    ty::{
        self,
        fast_reject::{self, simplify_type, SimplifiedType},
        FloatTy, GenericArg, Instance, IntTy, ParamEnv, TyCtxt, UintTy,
    },
};
use rustc_parse::new_parser_from_source_str;
use rustc_span::Symbol;

#[derive(Debug, Clone, Copy)]
pub enum Res {
    Def(DefKind, DefId),
    PrimTy(PrimTy),
}

#[derive(Clone, Debug)]
pub enum ResolutionError {
    CannotResolvePrimitiveType(Symbol),
    PathIsEmpty,
    CouldNotFindChild {
        item: DefId,
        segment: Symbol,
        search_space: SearchSpace,
    },
    EmptyStarts,
    UnconvertibleRes(def::Res),
    CouldNotResolveCrate(Symbol),
    UnsupportedType(Ty),
}

pub type Result<T> = std::result::Result<T, ResolutionError>;

#[derive(Clone, Debug)]
pub enum SearchSpace {
    InherentImpl,
    Mod,
}

impl Res {
    fn from_def_res(res: def::Res) -> Result<Self> {
        match res {
            def::Res::Def(k, i) => Ok(Res::Def(k, i)),
            def::Res::PrimTy(t) => Ok(Res::PrimTy(t)),
            other => Err(ResolutionError::UnconvertibleRes(other)),
        }
    }

    pub fn def_id(&self) -> DefId {
        if let Res::Def(_, id) = self {
            *id
        } else {
            panic!("Not a def")
        }
    }
}

fn as_primitive_ty(name: Symbol) -> Option<SimplifiedType> {
    match name.as_str() {
        "bool" => Some(SimplifiedType::Bool),
        "char" => Some(SimplifiedType::Char),
        "str" => Some(SimplifiedType::Str),
        "array" => Some(SimplifiedType::Array),
        "slice" => Some(SimplifiedType::Slice),
        "const_ptr" => Some(SimplifiedType::Ptr(Mutability::Not)),
        "mut_ptr" => Some(SimplifiedType::Ptr(Mutability::Mut)),
        "isize" => Some(SimplifiedType::Int(IntTy::Isize)),
        "i8" => Some(SimplifiedType::Int(IntTy::I8)),
        "i16" => Some(SimplifiedType::Int(IntTy::I16)),
        "i32" => Some(SimplifiedType::Int(IntTy::I32)),
        "i64" => Some(SimplifiedType::Int(IntTy::I64)),
        "i128" => Some(SimplifiedType::Int(IntTy::I128)),
        "usize" => Some(SimplifiedType::Uint(UintTy::Usize)),
        "u8" => Some(SimplifiedType::Uint(UintTy::U8)),
        "u16" => Some(SimplifiedType::Uint(UintTy::U16)),
        "u32" => Some(SimplifiedType::Uint(UintTy::U32)),
        "u64" => Some(SimplifiedType::Uint(UintTy::U64)),
        "u128" => Some(SimplifiedType::Uint(UintTy::U128)),
        "f32" => Some(SimplifiedType::Float(FloatTy::F32)),
        "f64" => Some(SimplifiedType::Float(FloatTy::F64)),
        _ => None,
    }
}

fn find_primitive_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: Symbol,
) -> impl Iterator<Item = DefId> + 'tcx {
    let Some(ty) = as_primitive_ty(name) else {
        return [].iter().copied();
    };

    tcx.incoherent_impls(ty).iter().copied()
}

/// A small helper wrapper around [`def_path_res`] that represents a common way
/// that `def_path_res` is used. In the case of errors they are reported to the
/// user and `None` is returned so the caller has the option of making progress
/// before exiting.
pub fn expect_resolve_string_to_def_id(tcx: TyCtxt, path: &str, relaxed: bool) -> Option<DefId> {
    let report_err = if relaxed {
        |tcx: TyCtxt<'_>, err: String| {
            tcx.sess.warn(err);
        }
    } else {
        |tcx: TyCtxt<'_>, err| {
            tcx.sess.err(err);
        }
    };
    let mut parser = new_parser_from_source_str(
        &tcx.sess.parse_sess,
        rustc_span::FileName::Custom("expect resolve".to_string()),
        path.to_string(),
    );
    let qpath = parser.parse_expr().map_err(|mut e| e.emit()).ok()?;
    if parser.token.kind != TokenKind::Eof {
        report_err(tcx, format!("Tokens left over after parsing path {path}"));
        return None;
    }

    let ExprKind::Path(slf, rest) = &qpath.kind else {
        report_err(tcx, format!("Expected path expression, got {path}"));
        return None;
    };

    let res = def_path_res(tcx, slf.as_deref(), &rest.segments)
        .map_err(|e| report_err(tcx, format!("Could not resolve {path}: {e:?}")))
        .ok()?;
    match res {
        Res::Def(_, did) => Some(did),
        other => {
            let msg = format!("expected {path} to resolve to an item, got {other:?}");
            report_err(tcx, msg);
            None
        }
    }
}

fn item_child_by_name(tcx: TyCtxt<'_>, def_id: DefId, name: Symbol) -> Option<Result<Res>> {
    if let Some(local_id) = def_id.as_local() {
        local_item_children_by_name(tcx, local_id, name)
    } else {
        non_local_item_children_by_name(tcx, def_id, name)
    }
}

fn non_local_item_children_by_name(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    name: Symbol,
) -> Option<Result<Res>> {
    match tcx.def_kind(def_id) {
        DefKind::Mod | DefKind::Enum | DefKind::Trait => tcx
            .module_children(def_id)
            .iter()
            .find(|item| item.ident.name == name)
            .map(|child| Res::from_def_res(child.res.expect_non_local())),
        DefKind::Impl { of_trait: false } => tcx
            .associated_item_def_ids(def_id)
            .iter()
            .copied()
            .find(|assoc_def_id| tcx.item_name(*assoc_def_id) == name)
            .map(|assoc_def_id| Ok(Res::Def(tcx.def_kind(assoc_def_id), assoc_def_id))),
        _ => None,
    }
}

fn local_item_children_by_name(
    tcx: TyCtxt<'_>,
    local_id: LocalDefId,
    name: Symbol,
) -> Option<Result<Res>> {
    let hir = tcx.hir();

    let root_mod;
    let item_kind = match hir.find_by_def_id(local_id) {
        Some(Node::Crate(r#mod)) => {
            root_mod = ItemKind::Mod(r#mod);
            &root_mod
        }
        Some(Node::Item(item)) => &item.kind,
        _ => return None,
    };

    let res = |def_id: LocalDefId| Ok(Res::Def(tcx.def_kind(def_id), def_id.to_def_id()));

    match item_kind {
        ItemKind::Mod(r#mod) => r#mod
            .item_ids
            .iter()
            .find(|&item_id| hir.item(*item_id).ident.name == name)
            .map(|&item_id| res(item_id.owner_id.def_id)),
        ItemKind::Impl(r#impl) => r#impl
            .items
            .iter()
            .find(|item| item.ident.name == name)
            .map(|&ImplItemRef { id, .. }| res(id.owner_id.def_id)),
        ItemKind::Trait(.., trait_item_refs) => trait_item_refs
            .iter()
            .find(|item| item.ident.name == name)
            .map(|&TraitItemRef { id, .. }| res(id.owner_id.def_id)),
        _ => None,
    }
}

fn find_crates(tcx: TyCtxt<'_>, name: Symbol) -> impl Iterator<Item = DefId> + '_ {
    tcx.crates(())
        .iter()
        .copied()
        .filter(move |&num| tcx.crate_name(num) == name)
        .map(CrateNum::as_def_id)
}

fn resolve_ty<'tcx>(tcx: TyCtxt<'tcx>, t: &Ty) -> Result<ty::Ty<'tcx>> {
    match &t.kind {
        TyKind::Path(qslf, pth) => {
            let adt = def_path_res(tcx, qslf.as_deref(), pth.segments.as_slice())?;
            Ok(ty::Ty::new_adt(
                tcx,
                tcx.adt_def(adt.def_id()),
                ty::List::empty(),
            ))
        }
        _ => Err(ResolutionError::UnsupportedType(t.clone())),
    }
}

/// Main algorithm lifted from `clippy_utils`. I've made additions so this can
/// handle some qualified paths.
///
/// ## Caveats
///
/// Resolution is a rabbit hole that is easy to get lost in. To avoid spending
/// inordinate amounts of time on this, I have eschewed some features and
/// niceties that didn't seem pressing. What follows is a numbered list of such
/// features. Each index in this list is later mentioned in code comments at
/// locations that are likely the best place to get started for implementing the
/// issue in question.
///
/// 1. All local paths must start with `crate`. If the path has only one segment
///    this function assumes it is a primitive type and tries to resolve it as
///    such. E.g. you need to do `crate::MyStruct::method` and `<crate::MyStruct
///    as std::clone::Clone>::clone`.
/// 3. Generics are not supported. If you want to reference a path like
///    `<std::vec::Vec<T> as std::iter::Extend>::extend`, simply don't add the
///    `<T>`. Note though that you need to ensure that there is only one
///    matching method in this case. If the generics would be needed to
///    disambiguate the instances, one of them is instead returned
///    non-deterministically.
/// 2. It probably cannot resolve a qualified path if the base is a primitive
///    type. E.g. `usize::abs_diff` resolves but `<usize>::abs_diff` does not.
pub fn def_path_res(tcx: TyCtxt, qself: Option<&QSelf>, path: &[PathSegment]) -> Result<Res> {
    let no_generics_supported = |segment: &PathSegment| {
        if segment.args.is_some() {
            tcx.sess.err(format!(
                "Generics are not supported in this position: {segment:?}"
            ));
        }
    };
    let (starts, path): (_, &[PathSegment]) = match qself {
        None => match path {
            [primitive] => {
                /* Start here for issue 1 */
                let sym = primitive.ident.name;
                return PrimTy::from_name(sym)
                    .map(Res::PrimTy)
                    .ok_or(ResolutionError::CannotResolvePrimitiveType(sym));
            }
            [base, ref path @ ..] => {
                /* This is relevant for issue 2 */
                no_generics_supported(base);
                let base_name = base.ident.name;
                let local_crate =
                    if tcx.crate_name(LOCAL_CRATE) == base_name || base_name.as_str() == "crate" {
                        Some(LOCAL_CRATE.as_def_id())
                    } else {
                        None
                    };
                (
                    Box::new(
                        find_primitive_impls(tcx, base_name)
                            .chain(find_crates(tcx, base_name))
                            .chain(local_crate),
                    ) as Box<dyn Iterator<Item = DefId>>,
                    path,
                )
            }
            [] => return Err(ResolutionError::PathIsEmpty),
        },
        Some(slf) => (
            if slf.position == 0 {
                /* this is relevant for 3 */
                let TyKind::Path(qslf, pth) = &slf.ty.kind else {
                    return Err(ResolutionError::UnsupportedType((*slf.ty).clone()));
                };
                let ty = def_path_res(tcx, qslf.as_deref(), &pth.segments)?;
                let impls = tcx.inherent_impls(ty.def_id());
                Box::new(impls.into_iter().copied()) as Box<_>
            } else {
                let r#trait = def_path_res(tcx, None, &path[..slf.position])?;
                let r#type = resolve_ty(tcx, &slf.ty)?;
                let mut impls = vec![];
                /* This is relevant for issue 2 */
                tcx.for_each_relevant_impl(r#trait.def_id(), r#type, |i| impls.push(i));
                Box::new(impls.into_iter()) as Box<_>
            },
            &path[slf.position..],
        ),
    };

    let mut last = Err(ResolutionError::EmptyStarts);
    for first in starts {
        last = path
            .iter()
            // for each segment, find the child item
            .try_fold(Res::Def(tcx.def_kind(first), first), |res, segment| {
                no_generics_supported(segment);
                let segment = segment.ident.name;
                let def_id = res.def_id();
                if let Some(item) = item_child_by_name(tcx, def_id, segment) {
                    item
                } else if matches!(res, Res::Def(DefKind::Enum | DefKind::Struct, _)) {
                    // it is not a child item so check inherent impl items
                    tcx.inherent_impls(def_id)
                        .iter()
                        .find_map(|&impl_def_id| item_child_by_name(tcx, impl_def_id, segment))
                        .unwrap_or(Err(ResolutionError::CouldNotFindChild {
                            item: def_id,
                            segment,
                            search_space: SearchSpace::InherentImpl,
                        }))
                } else {
                    Err(ResolutionError::CouldNotFindChild {
                        item: def_id,
                        segment,
                        search_space: SearchSpace::Mod,
                    })
                }
            });

        if last.is_ok() {
            return last;
        }
    }
    last
}
