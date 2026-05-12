use std::{hash::Hash, panic};

use ast::Mutability;
use hir::{
    ItemKind, Node, PrimTy,
    def::{self, DefKind},
    def_id::CrateNum,
    def_id::LOCAL_CRATE,
    def_id::LocalDefId,
};
use rustc_ast::{
    self as ast, AngleBracketedArg, ExprKind, GenericArg, GenericArgs, GenericBound, PathSegment,
    QSelf, TraitObjectSyntax, Ty, TyKind,
    token::TokenKind,
};
use rustc_data_structures::stable_hasher::StableHasher;
use rustc_hir::{self as hir, def_id::DefId};
use rustc_middle::ty::{self, FloatTy, IntTy, TyCtxt, UintTy, fast_reject::SimplifiedType};
use rustc_parse::{lexer::StripTokens, new_parser_from_source_str};
use rustc_span::Symbol;
use tracing::{trace, warn};

#[derive(Debug, Clone, Copy)]
pub enum Res {
    Def(DefKind, DefId),
    PrimTy(SimplifiedType),
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
    ParseError(String),
    NoImplsFound(DefId, Ty),
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
            def::Res::PrimTy(t) => Ok(Res::PrimTy(prim_ty_to_simp_ty(t))),
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

    pub fn as_string(&self, tcx: TyCtxt<'_>) -> String {
        match self {
            Res::Def(_, id) => tcx.def_path_str(*id),
            Res::PrimTy(ty) => format!("{ty:?}"),
        }
    }
}

fn prim_ty_to_simp_ty(pt: PrimTy) -> SimplifiedType {
    match pt {
        PrimTy::Bool => SimplifiedType::Bool,
        PrimTy::Char => SimplifiedType::Char,
        PrimTy::Str => SimplifiedType::Str,
        PrimTy::Int(i) => SimplifiedType::Int(i),
        PrimTy::Uint(u) => SimplifiedType::Uint(u),
        PrimTy::Float(f) => SimplifiedType::Float(f),
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

fn find_primitive_impls(tcx: TyCtxt<'_>, name: Symbol) -> impl Iterator<Item = DefId> + '_ {
    let Some(ty) = as_primitive_ty(name) else {
        return [].iter().copied();
    };

    tcx.incoherent_impls(ty).iter().copied()
}

/// A small helper wrapper around [`def_path_res`] that represents a common way
/// that `def_path_res` is used. In the case of errors they are reported to the
/// user and `None` is returned so the caller has the option of making progress
/// before exiting.
pub fn expect_resolve_string_to_def_id(tcx: TyCtxt, path: &str, relaxed: bool) -> Vec<DefId> {
    report_resolution_err(tcx, path, relaxed, resolve_string_to_def_id(tcx, path))
}

pub fn report_resolution_err(
    tcx: TyCtxt<'_>,
    path: &str,
    relaxed: bool,
    obj: Result<Vec<Res>>,
) -> Vec<DefId> {
    let report_err = if relaxed {
        |tcx: TyCtxt<'_>, err: String| {
            tcx.dcx().warn(err);
        }
    } else {
        |tcx: TyCtxt<'_>, err| {
            tcx.dcx().err(err);
        }
    };
    let Some(res) = obj
        .map_err(|e| report_err(tcx, format!("Could not resolve {path}: {e:?}")))
        .ok()
    else {
        return vec![];
    };
    res.into_iter()
        .filter_map(|res| match res {
            Res::Def(_, did) => Some(did),
            other => {
                let msg = format!("expected {path} to resolve to an item, got {other:?}");
                report_err(tcx, msg);
                None
            }
        })
        .collect()
}

pub fn resolve_string_to_def_id(tcx: TyCtxt, path: &str) -> Result<Vec<Res>> {
    let mut hasher = StableHasher::new();
    path.hash(&mut hasher);
    let mut parser = new_parser_from_source_str(
        &tcx.sess.psess,
        rustc_span::FileName::Anon(hasher.finish()),
        path.to_string(),
        StripTokens::Nothing,
    )
    .unwrap();
    let qpath = parser.parse_expr().map_err(|e| {
        e.emit();
        ResolutionError::ParseError("failed to parse expression".to_string())
    })?;
    if parser.token.kind != TokenKind::Eof {
        return Err(ResolutionError::ParseError(format!(
            "Tokens left over after parsing path {path}"
        )));
    }

    let ExprKind::Path(slf, rest) = &qpath.kind else {
        return Err(ResolutionError::ParseError(format!(
            "Expected path expression, got {path}"
        )));
    };

    def_path_res(tcx, slf.as_deref(), &rest.segments)
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
        DefKind::Impl { .. } => tcx
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
    let root_mod;
    let item_kind = match tcx.hir_node_by_def_id(local_id) {
        Node::Crate(r#mod) => {
            root_mod = ItemKind::Mod(rustc_span::Ident::dummy(), r#mod);
            &root_mod
        }
        Node::Item(item) => &item.kind,
        _ => return None,
    };

    let res = |def_id: LocalDefId| Ok(Res::Def(tcx.def_kind(def_id), def_id.to_def_id()));

    let item_matches_name = |did| tcx.opt_item_name(did).is_some_and(|n| n == name);

    match item_kind {
        ItemKind::Mod(_, r#mod) => r#mod
            .item_ids
            .iter()
            .find(|&item_id| item_matches_name(item_id.owner_id.def_id.to_def_id()))
            .map(|&item_id| res(item_id.owner_id.def_id)),
        ItemKind::Impl(r#impl) => r#impl
            .items
            .iter()
            .find(|item| item_matches_name(item.owner_id.def_id.to_def_id()))
            .map(|item| res(item.owner_id.def_id)),
        ItemKind::Trait(.., trait_item_refs) => trait_item_refs
            .iter()
            .find(|item| item_matches_name(item.owner_id.def_id.to_def_id()))
            .map(|item| res(item.owner_id.def_id)),
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
            let results = def_path_res(tcx, qslf.as_deref(), pth.segments.as_slice())?;
            let [adt] = results.as_slice() else {
                return Err(ResolutionError::UnsupportedType(t.clone()));
            };
            Ok(match adt {
                Res::Def(_, did) => ty::Ty::new_adt(tcx, tcx.adt_def(*did), ty::List::empty()),
                Res::PrimTy(simp) => match simp {
                    SimplifiedType::Bool => tcx.types.bool,
                    SimplifiedType::Char => tcx.types.char,
                    SimplifiedType::Str => tcx.types.str_,
                    SimplifiedType::Int(i) => ty::Ty::new_int(tcx, *i),
                    SimplifiedType::Uint(u) => ty::Ty::new_uint(tcx, *u),
                    SimplifiedType::Float(f) => ty::Ty::new_float(tcx, *f),
                    _ => return Err(ResolutionError::UnsupportedType(t.clone())),
                },
            })
        }
        TyKind::Tup(tys) => Ok(ty::Ty::new_tup(
            tcx,
            tys.iter()
                .map(|ty| resolve_ty(tcx, ty))
                .collect::<Result<Vec<_>>>()?
                .as_ref(),
        )),
        TyKind::Array(inner, const_) => {
            if !matches!(inner.kind, TyKind::Infer) {
                tcx.dcx()
                    .warn(format!("Ignoring non-wildcard slice type {inner:?}"));
            }
            if !matches!(const_.value.kind, rustc_ast::ExprKind::Underscore) {
                tcx.dcx()
                    .warn(format!("Ignoring const argument {const_:?} in array type"));
            }
            let our_len = 42;
            warn!(
                "Array types may not behave properly with instance markers because we always use the instance of arrays of length {our_len}"
            );
            Ok(ty::Ty::new_array(
                tcx,
                ty::Ty::new_param(tcx, 0, Symbol::intern("T")),
                our_len,
            ))
        }
        TyKind::Slice(inner) => {
            if !matches!(inner.kind, TyKind::Infer) {
                tcx.dcx()
                    .warn(format!("Ignoring non-wildcard slice type {inner:?}"));
            }
            Ok(ty::Ty::new_slice(
                tcx,
                ty::Ty::new_param(tcx, 0, Symbol::intern("T")),
            ))
        }
        TyKind::Ref(lt, mt) => {
            if lt.is_some() {
                tcx.dcx().warn("Ignoring lifetimes in reference types");
            }
            let inner = resolve_ty(tcx, &mt.ty)?;
            let lt = ty::Region::new_var(tcx, ty::RegionVid::ZERO);
            Ok(match mt.mutbl {
                hir::Mutability::Mut => ty::Ty::new_mut_ref(tcx, lt, inner),
                hir::Mutability::Not => ty::Ty::new_imm_ref(tcx, lt, inner),
            })
        }
        TyKind::Ptr(mt) => {
            let inner = resolve_ty(tcx, &mt.ty)?;
            Ok(match mt.mutbl {
                hir::Mutability::Mut => ty::Ty::new_mut_ptr(tcx, inner),
                hir::Mutability::Not => ty::Ty::new_imm_ptr(tcx, inner),
            })
        }
        _ => Err(ResolutionError::UnsupportedType(t.clone())),
    }
}

/// Pull just the `Ty` arguments out of an `AngleBracketed` generic-args
/// list, resolved to `ty::Ty`. Lifetimes, consts, and associated-item
/// constraints are silently skipped (a corner-cut: we only support
/// generic-arg-based inherent-impl disambiguation, not full generic-arg
/// plumbing). `Parenthesized` / `ParenthesizedElided` arg forms (`Fn(A,
/// B) -> C` and return-type-notation) aren't supported here and produce
/// an empty result, which the caller treats as "no filter to apply".
fn extract_angle_type_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    ga: &GenericArgs,
) -> Result<Vec<ty::Ty<'tcx>>> {
    let GenericArgs::AngleBracketed(ab) = ga else {
        return Ok(vec![]);
    };
    ab.args
        .iter()
        .filter_map(|arg| match arg {
            AngleBracketedArg::Arg(GenericArg::Type(ty)) => Some(resolve_ty(tcx, ty)),
            _ => None,
        })
        .collect()
}

/// Param-as-wildcard structural match: a `Param` on the *impl* side
/// accepts any supplied type. Used to filter `inherent_impls(adt_did)`
/// by whether each impl's `Self` substitution is compatible with a
/// supplied type. Coverage is intentionally partial; unsupported `Ty`
/// shapes return `false` (a safe error — the marker just won't bind).
fn match_ty_with_wildcard<'tcx>(supplied: ty::Ty<'tcx>, impl_ty: ty::Ty<'tcx>) -> bool {
    if matches!(impl_ty.kind(), ty::Param(_)) {
        return true;
    }
    match (supplied.kind(), impl_ty.kind()) {
        (ty::Adt(s_def, s_args), ty::Adt(i_def, i_args)) if s_def.did() == i_def.did() => {
            s_args.len() == i_args.len()
                && s_args.iter().zip(i_args.iter()).all(|(s, i)| match (s.kind(), i.kind()) {
                    (ty::GenericArgKind::Type(s), ty::GenericArgKind::Type(i)) => {
                        match_ty_with_wildcard(s, i)
                    }
                    // Lifetimes and consts: bail to equality. With the
                    // resolver's lifetime erasure (resolve_ty replaces
                    // refs' lifetimes with RegionVid::ZERO) this will
                    // typically mismatch for `&'a T` vs `&'b T`; matching
                    // those properly would need an InferCtxt.
                    _ => s == i,
                })
        }
        (ty::RawPtr(s_inner, s_mut), ty::RawPtr(i_inner, i_mut)) if s_mut == i_mut => {
            match_ty_with_wildcard(*s_inner, *i_inner)
        }
        (ty::Ref(_, s_inner, s_mut), ty::Ref(_, i_inner, i_mut)) if s_mut == i_mut => {
            match_ty_with_wildcard(*s_inner, *i_inner)
        }
        // Primitives and other leaf kinds: rely on `TyKind`-level equality.
        _ => supplied.kind() == impl_ty.kind(),
    }
}

/// Does the inherent impl's `Self`-type substitution match `supplied`
/// args? Operates on the impl's `Self` viewed via `tcx.type_of`, which
/// for `impl<T> AtomicPtr<T> { ... }` returns the alias-normalized
/// `Atomic<*mut T>` (with `T` a `Param`).
fn impl_self_args_match<'tcx>(
    tcx: TyCtxt<'tcx>,
    impl_def_id: DefId,
    supplied: &[ty::Ty<'tcx>],
) -> bool {
    let self_ty = tcx.type_of(impl_def_id).skip_binder();
    let ty::Adt(_, impl_args) = self_ty.kind() else {
        return false;
    };
    let impl_type_args: Vec<ty::Ty<'_>> = impl_args
        .iter()
        .filter_map(|a| match a.kind() {
            ty::GenericArgKind::Type(t) => Some(t),
            _ => None,
        })
        .collect();
    if supplied.len() != impl_type_args.len() {
        return false;
    }
    supplied
        .iter()
        .zip(impl_type_args.iter())
        .all(|(s, i)| match_ty_with_wildcard(*s, *i))
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
pub fn def_path_res(tcx: TyCtxt, qself: Option<&QSelf>, path: &[PathSegment]) -> Result<Vec<Res>> {
    trace!("Resolving {qself:?} {path:?}");
    let no_generics_supported = |segment: &PathSegment| {
        if segment.args.is_some() {
            tcx.dcx().err(format!(
                "Generics are not supported in this position: {segment:?}"
            ));
        }
    };
    let (starts, path): (_, &[PathSegment]) = match qself {
        None => match path {
            [primitive] => {
                /* Start here for issue 1 */
                let sym = primitive.ident.name;
                if let Some(sim_ty) = as_primitive_ty(sym) {
                    return Ok(vec![Res::PrimTy(sim_ty)]);
                } else {
                    (
                        Box::new(find_crates(tcx, sym)) as Box<dyn Iterator<Item = DefId>>,
                        &[],
                    )
                }
            }
            [base, path @ ..] => {
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
                let t = &*slf.ty;
                match &slf.ty.kind {
                    TyKind::Path(qslf, pth) => Box::new(
                        def_path_res(tcx, qslf.as_deref(), &pth.segments)?
                            .into_iter()
                            .flat_map(|def_id| tcx.inherent_impls(def_id.def_id()).iter().copied()),
                    )
                        as Box<dyn Iterator<Item = DefId>>,
                    TyKind::TraitObject(bounds, TraitObjectSyntax::Dyn) => {
                        let [GenericBound::Trait(t_ref)] = bounds.as_slice() else {
                            return Err(ResolutionError::UnsupportedType(t.clone()));
                        };
                        let resolved_trait =
                            def_path_res(tcx, None, &t_ref.trait_ref.path.segments)?;
                        let any_sym = Symbol::intern("Any");
                        let Some(t) = resolved_trait
                            .iter()
                            .find(|t| tcx.is_diagnostic_item(any_sym, t.def_id()))
                        else {
                            return Err(ResolutionError::UnsupportedType(t.clone()));
                        };
                        let impls = tcx.inherent_impls(t.def_id());
                        Box::new(impls.iter().cloned()) as Box<_>
                    }
                    _ => return Err(ResolutionError::UnsupportedType((*slf.ty).clone())),
                }
            } else {
                let mut impls = vec![];
                for r#trait in def_path_res(tcx, None, &path[..slf.position])? {
                    let r#type = resolve_ty(tcx, &slf.ty)?;
                    /* This is relevant for issue 2 */
                    tcx.for_each_relevant_impl(r#trait.def_id(), r#type, |i| impls.push(i));
                    if impls.is_empty() {
                        if tcx
                            .lang_items()
                            .clone_fn()
                            .is_some_and(|c| c == r#trait.def_id())
                            && r#type.is_unit()
                        {
                            tcx.dcx().err("Cannot assign markers to the Clone instance of (), is not a real function");
                        }
                        return Err(ResolutionError::NoImplsFound(
                            r#trait.def_id(),
                            (*slf.ty).clone(),
                        ));
                    }
                }
                Box::new(impls.into_iter()) as Box<_>
            },
            &path[slf.position..],
        ),
    };

    let starts = starts.collect::<Vec<_>>();
    trace!("starts: {:?}", starts);
    let starts = starts.into_iter();

    let empty_err = Err(if let Some(f) = path.first() {
        ResolutionError::CouldNotResolveCrate(f.ident.name)
    } else {
        ResolutionError::EmptyStarts
    });
    let mut found = starts
        .map(|first| -> Result<Res> {
            let mut res = Res::Def(tcx.def_kind(first), first);
            // Generic args attached to the segment that produced `res`.
            // Used at the inherent-impl-descent step below to filter
            // `inherent_impls(adt_did)` by `Self`-type compatibility,
            // disambiguating which `impl<T> Foo<T>` block the marker
            // should bind to (e.g. `Atomic::<*mut u8>::new`).
            let mut prev_args: Option<&GenericArgs> = None;
            for segment in path.iter() {
                let segment_name = segment.ident.name;
                let def_id = res.def_id();
                let next = if let Some(item) = item_child_by_name(tcx, def_id, segment_name) {
                    item
                } else {
                    // Either a struct/enum (descend into its inherent impls)
                    // or a type alias (normalize to its target ADT first and
                    // use the alias's own substitution as a default filter,
                    // so `AtomicPtr::new` — alias of `Atomic<*mut T>` — picks
                    // the `*mut T` impl rather than nondeterministically the
                    // first overload).
                    let (adt_did, alias_filter) = match res {
                        Res::Def(DefKind::Enum | DefKind::Struct, _) => (def_id, None),
                        Res::Def(DefKind::TyAlias, _) => {
                            let target = tcx.type_of(def_id).skip_binder();
                            let ty::Adt(adt_def, args) = target.kind() else {
                                return Err(ResolutionError::CouldNotFindChild {
                                    item: def_id,
                                    segment: segment_name,
                                    search_space: SearchSpace::Mod,
                                });
                            };
                            let type_args: Vec<ty::Ty<'_>> = args
                                .iter()
                                .filter_map(|a| match a.kind() {
                                    ty::GenericArgKind::Type(t) => Some(t),
                                    _ => None,
                                })
                                .collect();
                            (adt_def.did(), Some(type_args))
                        }
                        _ => {
                            return Err(ResolutionError::CouldNotFindChild {
                                item: def_id,
                                segment: segment_name,
                                search_space: SearchSpace::Mod,
                            });
                        }
                    };
                    // Explicit segment generics override alias-derived
                    // filtering. Failing to extract segment args is a
                    // safe error: skip the filter and behave like before
                    // (find_map first-match), per `_internal_can_fail_…`.
                    let segment_args = prev_args
                        .and_then(|ga| extract_angle_type_args(tcx, ga).ok());
                    let supplied_args: Option<&[ty::Ty<'_>]> =
                        segment_args.as_deref().or(alias_filter.as_deref());
                    let impls = tcx.inherent_impls(adt_did);
                    let candidate = impls.iter().find_map(|&impl_def_id| {
                        if let Some(args) = supplied_args
                            && !impl_self_args_match(tcx, impl_def_id, args)
                        {
                            return None;
                        }
                        item_child_by_name(tcx, impl_def_id, segment_name)
                    });
                    candidate.unwrap_or(Err(ResolutionError::CouldNotFindChild {
                        item: def_id,
                        segment: segment_name,
                        search_space: SearchSpace::InherentImpl,
                    }))
                };
                res = next?;
                prev_args = segment.args.as_deref();
            }
            Ok(res)
        })
        .collect::<Vec<_>>();

    if found.is_empty() {
        empty_err
    } else if found.iter().all(|f| f.is_err()) {
        found.pop().unwrap().map(|_| vec![])
    } else {
        Ok(found
            .into_iter()
            .filter_map(|f| f.ok())
            .inspect(|res| {
                trace!("  Resolved to {res:?}");
                if let Res::Def(_, did) = res {
                    trace!("    {} at {:?}", tcx.def_path_str(*did), tcx.def_span(*did));
                }
            })
            .collect())
    }
}
