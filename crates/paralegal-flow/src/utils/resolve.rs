use ast::Mutability;
use rustc_ast as ast;
use rustc_hir::def_id::DefId;
use rustc_hir::{
    def::{self, DefKind},
    def_id::CrateNum,
    def_id::LocalDefId,
    def_id::LOCAL_CRATE,
    ImplItemRef, ItemKind, Node, PrimTy, TraitItemRef,
};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Symbol;
use ty::{fast_reject::SimplifiedType, FloatTy, IntTy, UintTy};

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

fn find_primitive_impls<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> impl Iterator<Item = DefId> + 'tcx {
    let ty = match name {
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
    let segment_vec = path.split("::").collect::<Vec<_>>();
    let report_err = if relaxed {
        |tcx: TyCtxt<'_>, err: String| {
            tcx.sess.warn(err);
        }
    } else {
        |tcx: TyCtxt<'_>, err| {
            tcx.sess.err(err);
        }
    };
    let res = def_path_res(tcx, &segment_vec)
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

    let (base, path) = match *path {
        [primitive] => {
            let sym = Symbol::intern(primitive);
            return PrimTy::from_name(sym)
                .map(Res::PrimTy)
                .ok_or(ResolutionError::CannotResolvePrimitiveType(sym));
        }
        [base, ref path @ ..] => (base, path),
        [] => return Err(ResolutionError::PathIsEmpty),
    };

    let local_crate = if tcx.crate_name(LOCAL_CRATE) == Symbol::intern(base) || base == "crate" {
        Some(LOCAL_CRATE.as_def_id())
    } else {
        None
    };

    fn find_crates(tcx: TyCtxt<'_>, name: Symbol) -> impl Iterator<Item = DefId> + '_ {
        tcx.crates(())
            .iter()
            .copied()
            .filter(move |&num| tcx.crate_name(num) == name)
            .map(CrateNum::as_def_id)
    }

    let starts = find_primitive_impls(tcx, base)
        .chain(find_crates(tcx, Symbol::intern(base)))
        .chain(local_crate)
        .map(|id| Res::Def(tcx.def_kind(id), id));
    let mut last = Err(ResolutionError::EmptyStarts);
    for first in starts {
        last = path
            .iter()
            .copied()
            // for each segment, find the child item
            .try_fold(first, |res, segment| {
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
