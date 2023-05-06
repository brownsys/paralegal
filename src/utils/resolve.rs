use crate::{ast, hir, ty, DefId, Symbol, TyCtxt};
use ast::Mutability;
use hir::{
    def::{DefKind, Res},
    def_id::CrateNum,
    def_id::LocalDefId,
    def_id::LOCAL_CRATE,
    ImplItemRef, ItemKind, Mod, Node, PrimTy, TraitItemRef,
};
use ty::{fast_reject::SimplifiedTypeGen::*, FloatTy, IntTy, UintTy};

/// Lifted from `clippy_utils`
pub fn def_path_res(tcx: TyCtxt, path: &[&str]) -> Res {
    fn item_child_by_name(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> Option<Res> {
        if let Some(local_id) = def_id.as_local() {
            local_item_children_by_name(tcx, local_id, name)
        } else {
            non_local_item_children_by_name(tcx, def_id, name)
        }
    }

    fn non_local_item_children_by_name(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> Option<Res> {
        match tcx.def_kind(def_id) {
            DefKind::Mod | DefKind::Enum | DefKind::Trait => tcx
                .module_children(def_id)
                .iter()
                .find(|item| item.ident.name.as_str() == name)
                .map(|child| child.res.expect_non_local()),
            DefKind::Impl => tcx
                .associated_item_def_ids(def_id)
                .iter()
                .copied()
                .find(|assoc_def_id| tcx.item_name(*assoc_def_id).as_str() == name)
                .map(|assoc_def_id| Res::Def(tcx.def_kind(assoc_def_id), assoc_def_id)),
            _ => None,
        }
    }

    fn local_item_children_by_name(
        tcx: TyCtxt<'_>,
        local_id: LocalDefId,
        name: &str,
    ) -> Option<Res> {
        let hir = tcx.hir();

        let root_mod;
        let item_kind = match hir.find_by_def_id(local_id) {
            Some(Node::Crate(r#mod)) => {
                root_mod = ItemKind::Mod(Mod {
                    spans: r#mod.spans.clone(),
                    item_ids: r#mod.item_ids.clone(),
                });
                &root_mod
            }
            Some(Node::Item(item)) => &item.kind,
            _ => return None,
        };

        let res = |def_id: LocalDefId| Res::Def(tcx.def_kind(def_id), def_id.to_def_id());

        match item_kind {
            ItemKind::Mod(r#mod) => r#mod
                .item_ids
                .iter()
                .find(|&item_id| hir.item(*item_id).ident.name.as_str() == name)
                .map(|&item_id| res(item_id.def_id)),
            ItemKind::Impl(r#impl) => r#impl
                .items
                .iter()
                .find(|item| item.ident.name.as_str() == name)
                .map(|&ImplItemRef { id, .. }| res(id.def_id)),
            ItemKind::Trait(.., trait_item_refs) => trait_item_refs
                .iter()
                .find(|item| item.ident.name.as_str() == name)
                .map(|&TraitItemRef { id, .. }| res(id.def_id)),
            _ => None,
        }
    }

    fn find_primitive<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> impl Iterator<Item = DefId> + 'tcx {
        let single = |ty| tcx.incoherent_impls(ty).iter().copied();
        let empty = || [].iter().copied();
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
            return PrimTy::from_name(Symbol::intern(primitive)).map_or(Res::Err, Res::PrimTy);
        }
        _ => return Res::Err,
    };

    let local_crate = if tcx.crate_name(LOCAL_CRATE) == Symbol::intern(base) || base == "crate" {
        Some(LOCAL_CRATE.as_def_id())
    } else {
        None
    };

    let starts = find_primitive(tcx, base)
        .chain(find_crate(tcx, base))
        .chain(local_crate)
        .filter_map(|id| item_child_by_name(tcx, id, first));

    for first in starts {
        let last = path
            .iter()
            .copied()
            // for each segment, find the child item
            .try_fold(first, |res, segment| {
                let def_id = res.def_id();
                if let Some(item) = item_child_by_name(tcx, def_id, segment) {
                    Some(item)
                } else if matches!(res, Res::Def(DefKind::Enum | DefKind::Struct, _)) {
                    // it is not a child item so check inherent impl items
                    tcx.inherent_impls(def_id)
                        .iter()
                        .find_map(|&impl_def_id| item_child_by_name(tcx, impl_def_id, segment))
                } else {
                    None
                }
            });

        if let Some(last) = last {
            return last;
        }
    }

    Res::Err
}
