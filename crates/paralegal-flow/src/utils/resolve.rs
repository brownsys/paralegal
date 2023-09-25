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
use ty::{fast_reject::SimplifiedType::*, FloatTy, IntTy, UintTy};

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
        let single = |ty| Some(tcx.incoherent_impls(ty));
        let empty = || None;
        match name {
            "bool" => single(BoolSimplifiedType),
            "char" => single(CharSimplifiedType),
            "str" => single(StrSimplifiedType),
            "array" => single(ArraySimplifiedType),
            "slice" => single(SliceSimplifiedType),
            // FIXME: rustdoc documents these two using just `pointer`.
            //
            // Maybe this is something we should do here too.
            "const_ptr" => single(PtrSimplifiedType(Mutability::Not)),
            "mut_ptr" => single(PtrSimplifiedType(Mutability::Mut)),
            "isize" => single(IntSimplifiedType(IntTy::Isize)),
            "i8" => single(IntSimplifiedType(IntTy::I8)),
            "i16" => single(IntSimplifiedType(IntTy::I16)),
            "i32" => single(IntSimplifiedType(IntTy::I32)),
            "i64" => single(IntSimplifiedType(IntTy::I64)),
            "i128" => single(IntSimplifiedType(IntTy::I128)),
            "usize" => single(UintSimplifiedType(UintTy::Usize)),
            "u8" => single(UintSimplifiedType(UintTy::U8)),
            "u16" => single(UintSimplifiedType(UintTy::U16)),
            "u32" => single(UintSimplifiedType(UintTy::U32)),
            "u64" => single(UintSimplifiedType(UintTy::U64)),
            "u128" => single(UintSimplifiedType(UintTy::U128)),
            "f32" => single(FloatSimplifiedType(FloatTy::F32)),
            "f64" => single(FloatSimplifiedType(FloatTy::F64)),
            _ => empty(),
        }
    }
    fn find_crate(tcx: TyCtxt<'_>, name: &str) -> Option<DefId> {
        tcx.crates(())
            .iter()
            .copied()
            .find(|&num| tcx.crate_name(num).as_str() == name)
            .map(CrateNum::as_def_id)
    }

    let (base, first, path) = match *path {
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
