use std::borrow::Cow;

use crate::{ast, hir, ty, DefId, Symbol, TyCtxt};
use ast::Mutability;
use hir::{
    def::{self, DefKind},
    def_id::CrateNum,
    def_id::LocalDefId,
    def_id::LOCAL_CRATE,
    ImplItemRef, ItemKind, Node, PrimTy, TraitItemRef,
};
use ty::{fast_reject::SimplifiedType::{self, *}, FloatTy, IntTy, UintTy};

#[derive(Debug, Clone, Copy)]
pub enum Res {
    Def(DefKind, DefId),
    PrimTy(PrimTy),
}

#[derive(Clone, Debug)]
pub enum ResolutionError<'a> {
    CannotResolvePrimitiveType(Symbol),
    PathIsEmpty,
    CouldNotFindChild {
        item: DefId,
        segment: &'a str,
        search_space: SearchSpace,
    },
    EmptyStarts,
    UnconvertibleRes(def::Res),
    CouldNotResolveCrate(&'a str),
    BadlyFormedBaseCrateName(&'a str),
    ExpectedTraitInAsExpression(&'a str),
    DoesNotResolveToType(&'a str),
    NoTraitImplFound {
        r#trait: DefId,
        r#type: SimplifiedType,
    },
    TooManyImplsFor {
        r#trait: DefId,
        r#type: SimplifiedType,
    },
}

#[derive(Clone, Debug)]
pub enum SearchSpace {
    InherentImpl,
    Mod,
}

impl Res {
    fn from_def_res<'a>(res: def::Res) -> Result<Self, ResolutionError<'a>> {
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

/// Splits rust paths, e.g. `split_path_segments("std::vec::Vec") == ["std",
/// "vec", "Vec"]`.
/// 
/// But this is a bit fancier, because if the first element is encased in type
/// brackets `<>` then it is returned as one element, e.g.
/// `split_path_segments("<std::vec::Vec as
/// std::iter::IntoIterator>::into_iter") == ["<std::vec::Vec as
/// std::iter::IntoIterator>", "into_iter"]`.
/// 
/// Also ensures all whitespace of the output items has been stripped
fn split_path_segments(path: &str) -> impl Iterator<Item=&str> {
    let (first, rest) = if let Some(inner) = path.trim_start().strip_prefix('<') {
        assert!(!inner.contains('<'), "Nested type brackets are not supported: {path}");
        let (first, rest) = inner.split_once('>').unwrap_or_else(|| panic!("type brackets must be balanced: {path}"));
        let trimmed_rest = rest.trim_start();
        let rest = if let Some((empty, rest)) = trimmed_rest.split_once("::") {
            assert!(empty.trim_start().is_empty());
            rest
        } else {
            assert!(trimmed_rest.is_empty());
            ""
        };
        (first, rest)
    } else {
        path.split_once("::").unwrap_or((path, ""))
    };

    std::iter::once(first)
        .chain(rest.split("::"))
        .map(|s| s.trim())
}

fn resolve_trait_impl<'tcx, 'a>(tcx: TyCtxt<'tcx>, r#type: SimplifiedType, r#trait: DefId) -> Result<DefId, ResolutionError<'a>> {
    let impls = tcx.trait_impls_of(r#trait);
    if let [did] = impls.non_blanket_impls().get(&r#type)
        .ok_or(ResolutionError::NoTraitImplFound { r#trait, r#type })?
        .as_slice() {
        Ok(*did)
    } else {
        Err(ResolutionError::TooManyImplsFor { r#trait, r#type })
    }
}

/// Lifted from `clippy_utils`
pub fn def_path_res<'a>(tcx: TyCtxt, path: &[&'a str]) -> Result<Res, ResolutionError<'a>> {
    fn item_child_by_name<'a>(
        tcx: TyCtxt<'_>,
        def_id: DefId,
        name: &str,
    ) -> Option<Result<Res, ResolutionError<'a>>> {
        if let Some(local_id) = def_id.as_local() {
            local_item_children_by_name(tcx, local_id, name)
        } else {
            non_local_item_children_by_name(tcx, def_id, name)
        }
    }

    fn non_local_item_children_by_name<'a>(
        tcx: TyCtxt<'_>,
        def_id: DefId,
        name: &str,
    ) -> Option<Result<Res, ResolutionError<'a>>> {
        match tcx.def_kind(def_id) {
            DefKind::Mod | DefKind::Enum | DefKind::Trait => tcx
                .module_children(def_id)
                .iter()
                .find(|item| item.ident.name.as_str() == name)
                .map(|child| Res::from_def_res(child.res.expect_non_local())),
            DefKind::Impl { of_trait: false } => tcx
                .associated_item_def_ids(def_id)
                .iter()
                .copied()
                .find(|assoc_def_id| tcx.item_name(*assoc_def_id).as_str() == name)
                .map(|assoc_def_id| Ok(Res::Def(tcx.def_kind(assoc_def_id), assoc_def_id))),
            _ => None,
        }
    }

    fn local_item_children_by_name<'a>(
        tcx: TyCtxt<'_>,
        local_id: LocalDefId,
        name: &str,
    ) -> Option<Result<Res, ResolutionError<'a>>> {
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
                .find(|&item_id| hir.item(*item_id).ident.name.as_str() == name)
                .map(|&item_id| res(item_id.owner_id.def_id)),
            ItemKind::Impl(r#impl) => r#impl
                .items
                .iter()
                .find(|item| item.ident.name.as_str() == name)
                .map(|&ImplItemRef { id, .. }| res(id.owner_id.def_id)),
            ItemKind::Trait(.., trait_item_refs) => trait_item_refs
                .iter()
                .find(|item| item.ident.name.as_str() == name)
                .map(|&TraitItemRef { id, .. }| res(id.owner_id.def_id)),
            _ => None,
        }
    }

    fn find_primitive<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> Option<&'tcx [DefId]> {
        try_as_simplified_prim_ty(tcx, name).map(|prim| tcx.incoherent_impls(prim))
    }

    fn try_as_simplified_prim_ty<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> Option<SimplifiedType> {
        match name {
            "bool" => Some(BoolSimplifiedType),
            "char" => Some(CharSimplifiedType),
            "str" => Some(StrSimplifiedType),
            "array" => Some(ArraySimplifiedType),
            "slice" => Some(SliceSimplifiedType),
            // FIXME: rustdoc documents these two using just `pointer`.
            //
            // Maybe this is something we should do here too.
            "const_ptr" => Some(PtrSimplifiedType(Mutability::Not)),
            "mut_ptr" => Some(PtrSimplifiedType(Mutability::Mut)),
            "isize" => Some(IntSimplifiedType(IntTy::Isize)),
            "i8" => Some(IntSimplifiedType(IntTy::I8)),
            "i16" => Some(IntSimplifiedType(IntTy::I16)),
            "i32" => Some(IntSimplifiedType(IntTy::I32)),
            "i64" => Some(IntSimplifiedType(IntTy::I64)),
            "i128" => Some(IntSimplifiedType(IntTy::I128)),
            "usize" => Some(UintSimplifiedType(UintTy::Usize)),
            "u8" => Some(UintSimplifiedType(UintTy::U8)),
            "u16" => Some(UintSimplifiedType(UintTy::U16)),
            "u32" => Some(UintSimplifiedType(UintTy::U32)),
            "u64" => Some(UintSimplifiedType(UintTy::U64)),
            "u128" => Some(UintSimplifiedType(UintTy::U128)),
            "f32" => Some(FloatSimplifiedType(FloatTy::F32)),
            "f64" => Some(FloatSimplifiedType(FloatTy::F64)),
            _ => None,
        }
    }

    fn find_crate(tcx: TyCtxt<'_>, name: &str) -> Option<DefId> {
        tcx.crates(())
            .iter()
            .copied()
            .find(|&num| tcx.crate_name(num).as_str() == name)
            .map(CrateNum::as_def_id)
    }

    let (mut base, first, path) = match *path {
        [base, first, ref path @ ..] => (base, first, path),
        [primitive] => {
            let sym = Symbol::intern(primitive);
            return PrimTy::from_name(sym)
                .map(Res::PrimTy)
                .ok_or(ResolutionError::CannotResolvePrimitiveType(sym));
        }
        [] => return Err(ResolutionError::PathIsEmpty),
    };

    let local_crate = if tcx.crate_name(LOCAL_CRATE) == Symbol::intern(base) || base == "crate" {
        Some(Cow::Owned(vec![LOCAL_CRATE.as_def_id()]))
    } else {
        None
    };

    base = base.trim();

    if let Some(mut inner) = base.strip_prefix('<') {
        inner = base.strip_suffix('>').ok_or(ResolutionError::BadlyFormedBaseCrateName(base))?;
        if let Some((type_path, trait_path)) = inner.split_once("as") {
            let type_path_segments = split_path_segments(type_path).collect::<Vec<_>>();
            let r#type = 
                if let Some(prim) = (type_path_segments.len() == 1).then(|| try_as_simplified_prim_ty(tcx, type_path)).flatten() {
                    Ok(prim)
                } else if let Res::Def(_, res) = def_path_res(tcx, &type_path_segments)? {
                    Ok(SimplifiedType::AdtSimplifiedType(res))
                } else {
                    Err(ResolutionError::DoesNotResolveToType(type_path))
                }?;
            let trait_path_segments = split_path_segments(trait_path).collect::<Vec<_>>();
            let Res::Def(DefKind::Trait, r#trait) = def_path_res(tcx, &trait_path_segments)? else {
                return Err(ResolutionError::ExpectedTraitInAsExpression(trait_path))
            };
            let trait_impl = resolve_trait_impl(tcx, r#type, r#trait)?;
            assert!(path.is_empty(), "Additional path segments are not allowed when using trait resolution");
            item_child_by_name(tcx, trait_impl, first);
        } else {
            base = inner;
        }
    }

    let base_mods = find_primitive(tcx, base)
        .map(Cow::Borrowed)
        .or(local_crate)
        .or(find_crate(tcx, base).map(|i| Cow::Owned(vec![i])))
        .ok_or(ResolutionError::CouldNotResolveCrate(base))?;
    let starts = base_mods
        .iter()
        .filter_map(|id| item_child_by_name(tcx, *id, first));

    let mut last = Err(ResolutionError::EmptyStarts);
    for first in starts {
        last = path
            .iter()
            .copied()
            // for each segment, find the child item
            .try_fold(first?, |res, segment| {
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
