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
        self, fast_reject::SimplifiedType, FloatTy, GenericArg, Instance, IntTy, ParamEnv, TyCtxt,
        UintTy,
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

#[derive(Clone, Debug)]
pub enum SearchSpace {
    InherentImpl,
    Mod,
}

impl Res {
    fn from_def_res(res: def::Res) -> Result<Self, ResolutionError> {
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

fn find_primitive_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: Symbol,
) -> impl Iterator<Item = DefId> + 'tcx {
    let ty = match name.as_str() {
        "bool" => SimplifiedType::Bool,
        "char" => SimplifiedType::Char,
        "str" => SimplifiedType::Str,
        "array" => SimplifiedType::Array,
        "slice" => SimplifiedType::Slice,
        // FIXME: rustdoc documents these two using just `pointer`.
        //
        // Maybe this is something we should do here too.
        "const_ptr" => SimplifiedType::Ptr(Mutability::Not),
        "mut_ptr" => SimplifiedType::Ptr(Mutability::Mut),
        "isize" => SimplifiedType::Int(IntTy::Isize),
        "i8" => SimplifiedType::Int(IntTy::I8),
        "i16" => SimplifiedType::Int(IntTy::I16),
        "i32" => SimplifiedType::Int(IntTy::I32),
        "i64" => SimplifiedType::Int(IntTy::I64),
        "i128" => SimplifiedType::Int(IntTy::I128),
        "usize" => SimplifiedType::Uint(UintTy::Usize),
        "u8" => SimplifiedType::Uint(UintTy::U8),
        "u16" => SimplifiedType::Uint(UintTy::U16),
        "u32" => SimplifiedType::Uint(UintTy::U32),
        "u64" => SimplifiedType::Uint(UintTy::U64),
        "u128" => SimplifiedType::Uint(UintTy::U128),
        "f32" => SimplifiedType::Float(FloatTy::F32),
        "f64" => SimplifiedType::Float(FloatTy::F64),
        _ => return [].iter().copied(),
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

fn item_child_by_name(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    name: Symbol,
) -> Option<Result<Res, ResolutionError>> {
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
) -> Option<Result<Res, ResolutionError>> {
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
) -> Option<Result<Res, ResolutionError>> {
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

fn resolve_ty<'tcx>(tcx: TyCtxt<'tcx>, t: &Ty) -> Result<ty::Ty<'tcx>, ResolutionError> {
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

/// Lifted from `clippy_utils`
pub fn def_path_res(
    tcx: TyCtxt,
    qself: Option<&QSelf>,
    path: &[PathSegment],
) -> Result<Res, ResolutionError> {
    let (starts, path): (_, &[PathSegment]) = match qself {
        None => match path {
            [primitive] => {
                let sym = primitive.ident.name;
                return PrimTy::from_name(sym)
                    .map(Res::PrimTy)
                    .ok_or(ResolutionError::CannotResolvePrimitiveType(sym));
            }
            [base, ref path @ ..] => {
                let base_name = base.ident.name;
                let local_crate =
                    if tcx.crate_name(LOCAL_CRATE) == base_name || base_name.as_str() == "crate" {
                        Some(LOCAL_CRATE.as_def_id())
                    } else {
                        None
                    };
                (
                    Box::new(
                        find_primitive_impls(tcx, base.ident.name)
                            .chain(find_crates(tcx, base.ident.name))
                            .chain(local_crate),
                    ) as Box<dyn Iterator<Item = DefId>>,
                    path,
                )
            }
            [] => return Err(ResolutionError::PathIsEmpty),
        },
        Some(slf) => (
            {
                // handle position == 0
                let r#trait = def_path_res(tcx, None, &path[..slf.position])?;
                let r#type = resolve_ty(tcx, &slf.ty)?;
                let mut impls = vec![];
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
