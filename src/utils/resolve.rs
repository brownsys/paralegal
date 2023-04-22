use crate::{ast, hir, ty, DefId, Symbol, TyCtxt};
use ast::Mutability;
use hir::{
    def::{DefKind, Res},
    def_id::CrateNum,
    PrimTy,
};
use ty::{fast_reject::SimplifiedTypeGen::*, FloatTy, IntTy, UintTy};

/// Lifted from `clippy_utils`
pub fn def_path_res(tcx: TyCtxt, path: &[&str]) -> Res {
    fn item_child_by_name(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> Option<Res> {
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
    let starts = find_primitive(tcx, base)
        .chain(find_crate(tcx, base))
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
