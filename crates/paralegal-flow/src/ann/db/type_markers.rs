use crate::{utils::TyExt, Either};

use paralegal_spdg::Identifier;
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_middle::ty;

use super::{MarkerCtx, TypeMarkerElem, TypeMarkers};

impl<'tcx> MarkerCtx<'tcx> {
    /// All the markers applied to this type and its subtypes.
    ///
    /// Returns `(ann, (ty, did))` tuples which are the marker annotation `ann`,
    /// the specific type `ty` that it was applied to and the `did` [`Defid`] of
    /// that type that was used to look up the annotations.
    pub fn all_type_markers<'a>(
        &'a self,
        ty: ty::Ty<'tcx>,
    ) -> impl Iterator<Item = (Identifier, (ty::Ty<'tcx>, DefId))> + use<'a, 'tcx> {
        ty.walk().filter_map(|g| g.as_type()).flat_map(move |typ| {
            typ.defid()
                .into_iter()
                .flat_map(move |did| self.markers_on_self(did).zip(std::iter::repeat((typ, did))))
        })
    }

    pub fn shallow_type_markers<'a>(
        &'a self,
        key: ty::Ty<'tcx>,
    ) -> impl Iterator<Item = TypeMarkerElem> + use<'a, 'tcx> {
        use ty::*;
        let def_id = match key.kind() {
            Adt(def, _) => Some(def.did()),
            Alias(_, inner) => Some(inner.def_id),
            _ => None,
        };
        def_id
            .map(|def_id| self.markers_on_self(def_id).map(move |m| (def_id, m)))
            .into_iter()
            .flatten()
    }

    pub fn deep_type_markers<'a>(&'a self, key: ty::Ty<'tcx>) -> &'a TypeMarkers {
        self.db()
            .type_markers
            .get_maybe_recursive(&key, |key| {
                use ty::*;
                let mut markers = self.shallow_type_markers(key).collect::<FxHashSet<_>>();
                let dcx = self.tcx().dcx();
                match key.kind() {
                    Bool
                    | Char
                    | Int(_)
                    | Uint(_)
                    | Float(_)
                    | Foreign(_)
                    | Str
                    | FnDef { .. }
                    | FnPtr { .. }
                    | Closure { .. }
                    | Coroutine(..)
                    | CoroutineWitness(..)
                    | CoroutineClosure(..)
                    | Never
                    | Bound { .. }
                    | Error(_) => (),
                    Adt(def, generics) => markers.extend(self.type_markers_for_adt(def, generics)),
                    Tuple(tys) => {
                        markers.extend(tys.iter().flat_map(|ty| self.deep_type_markers(ty)))
                    }
                    Alias(_, _) => {
                        dcx.warn(format!("Alias type {key:?} remains. Was not normalized."));
                        return Box::new([]);
                    }
                    Pat(ty, _) => {
                        return self.deep_type_markers(*ty).into();
                    }
                    // We can't track indices so we simply overtaint to the entire array
                    Array(inner, _) | Slice(inner) => {
                        markers.extend(self.deep_type_markers(*inner))
                    }
                    RawPtr(ty, _) | Ref(_, ty, _) => markers.extend(self.deep_type_markers(*ty)),
                    Param(_) | Dynamic { .. } => {
                        dcx.warn(format!("Cannot determine markers for type {key:?}"))
                    }
                    Placeholder(_) | Infer(_) => {
                        dcx.fatal(format!("Did not expect this type here {key:?}"))
                    }
                }
                markers.into_iter().collect()
            })
            .map_or(&[], Box::as_ref)
    }

    fn type_markers_for_adt<'a>(
        &'a self,
        adt: &'a ty::AdtDef<'tcx>,
        generics: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ) -> impl Iterator<Item = &'a TypeMarkerElem> + use<'tcx, 'a> {
        if adt.is_phantom_data() {
            Either::Left(
                generics
                    .iter()
                    .filter_map(|g| g.as_type())
                    .flat_map(|t| self.deep_type_markers(t)),
            )
        } else {
            let tcx = self.tcx();
            Either::Right(
                adt.variants().iter_enumerated().flat_map(move |(_, vdef)| {
                    vdef.fields.iter_enumerated().flat_map(move |(_, fdef)| {
                        let f_ty = fdef.ty(tcx, generics);
                        self.deep_type_markers(f_ty)
                    })
                }), //.collect::<Vec<_>>(), //.into_iter(),
            )
        }
        .into_iter()
    }

    pub fn type_has_surface_markers(&self, ty: ty::Ty) -> Option<DefId> {
        let def_id = ty.defid()?;
        (self.markers_on_self(def_id).next().is_some()).then_some(def_id)
    }
}
