use std::{borrow::Cow, collections::hash_map::Entry, hash::Hash};

use either::Either;
use flowistry_pdg::rustc_portable::LocalDefId;
use itertools::Itertools;
use log::{debug, trace};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        tcx::PlaceTy, Body, HasLocalDecls, Local, Location, Place, ProjectionElem, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{
        self, EarlyBinder, GenericArg, GenericArgsRef, Instance, List, ParamEnv, Ty, TyCtxt, TyKind,
    },
};
use rustc_span::ErrorGuaranteed;
use rustc_type_ir::{fold::TypeFoldable, AliasKind};
use rustc_utils::{BodyExt, PlaceExt};

#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
pub enum FnResolution<'tcx> {
    Final(ty::Instance<'tcx>),
    Partial(DefId),
}

impl<'tcx> PartialOrd for FnResolution<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<'tcx> Ord for FnResolution<'tcx> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use FnResolution::*;
        match (self, other) {
            (Final(_), Partial(_)) => std::cmp::Ordering::Greater,
            (Partial(_), Final(_)) => std::cmp::Ordering::Less,
            (Partial(slf), Partial(otr)) => slf.cmp(otr),
            (Final(slf), Final(otr)) => match slf.def.cmp(&otr.def) {
                std::cmp::Ordering::Equal => slf.args.cmp(otr.args),
                result => result,
            },
        }
    }
}

impl<'tcx> FnResolution<'tcx> {
    pub fn def_id(self) -> DefId {
        match self {
            FnResolution::Final(f) => f.def_id(),
            FnResolution::Partial(p) => p,
        }
    }
}

impl<'tcx> std::fmt::Display for FnResolution<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FnResolution::Final(sub) => std::fmt::Debug::fmt(sub, f),
            FnResolution::Partial(p) => std::fmt::Debug::fmt(p, f),
        }
    }
}

/// Try and normalize the provided generics.
///
/// The purpose of this function is to test whether resolving these generics
/// will return an error. We need this because [`ty::Instance::resolve`] fails
/// with a hard error when this normalization fails (even though it returns
/// [`Result`]). However legitimate situations can arise in the code where this
/// normalization fails for which we want to report warnings but carry on with
/// the analysis which a hard error doesn't allow us to do.
fn test_generics_normalization<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    args: &'tcx ty::List<ty::GenericArg<'tcx>>,
) -> Result<(), ty::normalize_erasing_regions::NormalizationError<'tcx>> {
    tcx.try_normalize_erasing_regions(param_env, args)
        .map(|_| ())
}

pub fn try_resolve_function<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    param_env: ParamEnv<'tcx>,
    args: GenericArgsRef<'tcx>,
) -> FnResolution<'tcx> {
    let param_env = param_env.with_reveal_all_normalized(tcx);
    let make_opt = || {
        if let Err(e) = test_generics_normalization(tcx, param_env, args) {
            debug!("Normalization failed: {e:?}");
            return None;
        }
        Instance::resolve(tcx, param_env, def_id, args).unwrap()
    };

    match make_opt() {
        Some(inst) => FnResolution::Final(inst),
        None => FnResolution::Partial(def_id),
    }
}

pub fn is_non_default_trait_method(tcx: TyCtxt, function: DefId) -> Option<DefId> {
    let assoc_item = tcx.opt_associated_item(function)?;
    if assoc_item.container != ty::AssocItemContainer::TraitContainer
        || assoc_item.defaultness(tcx).has_value()
    {
        return None;
    }
    assoc_item.trait_item_def_id
}

impl<'tcx> FnResolution<'tcx> {
    pub fn try_monomorphize<'a, T>(
        self,
        tcx: TyCtxt<'tcx>,
        param_env: ParamEnv<'tcx>,
        t: &'a T,
    ) -> Cow<'a, T>
    where
        T: TypeFoldable<TyCtxt<'tcx>> + Clone,
    {
        match self {
            FnResolution::Partial(_) => Cow::Borrowed(t),
            FnResolution::Final(inst) => Cow::Owned(inst.subst_mir_and_normalize_erasing_regions(
                tcx,
                param_env,
                EarlyBinder::bind(tcx.erase_regions(t.clone())),
            )),
        }
    }
}

pub fn retype_place<'tcx>(
    orig: Place<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    def_id: DefId,
) -> Place<'tcx> {
    trace!("Retyping {orig:?} in context of {def_id:?}");

    let mut new_projection = Vec::new();
    let mut ty = PlaceTy::from_ty(body.local_decls()[orig.local].ty);
    let param_env = tcx.param_env_reveal_all_normalized(def_id);
    for elem in orig.projection.iter() {
        if matches!(
            ty.ty.kind(),
            TyKind::Alias(..) | TyKind::Param(..) | TyKind::Bound(..) | TyKind::Placeholder(..)
        ) {
            break;
        }

        // Don't continue if we reach a private field
        if let ProjectionElem::Field(field, _) = elem {
            if let Some(adt_def) = ty.ty.ty_adt_def() {
                let field = adt_def
                    .all_fields()
                    .nth(field.as_usize())
                    .unwrap_or_else(|| {
                        panic!("ADT for {:?} does not have field {field:?}", ty.ty);
                    });
                if !field.vis.is_accessible_from(def_id, tcx) {
                    break;
                }
            }
        }

        trace!(
            "    Projecting {:?}.{new_projection:?} : {:?} with {elem:?}",
            orig.local,
            ty.ty,
        );
        ty = ty.projection_ty_core(
            tcx,
            param_env,
            &elem,
            |_, field, _| match ty.ty.kind() {
                TyKind::Closure(_, args) => {
                    let upvar_tys = args.as_closure().upvar_tys();
                    upvar_tys.iter().nth(field.as_usize()).unwrap()
                }
                TyKind::Generator(_, args, _) => {
                    let upvar_tys = args.as_generator().upvar_tys();
                    upvar_tys.iter().nth(field.as_usize()).unwrap()
                }
                _ => ty.field_ty(tcx, field),
            },
            |_, ty| ty,
        );
        let elem = match elem {
            ProjectionElem::Field(field, _) => ProjectionElem::Field(field, ty.ty),
            elem => elem,
        };
        new_projection.push(elem);
    }

    let p = Place::make(orig.local, &new_projection, tcx);
    trace!("    Final translation: {p:?}");
    p
}

pub fn hashset_join<T: Hash + Eq + PartialEq + Clone>(
    hs1: &mut FxHashSet<T>,
    hs2: &FxHashSet<T>,
) -> bool {
    let orig_len = hs1.len();
    hs1.extend(hs2.iter().cloned());
    hs1.len() != orig_len
}

pub fn hashmap_join<K: Hash + Eq + PartialEq + Clone, V: Clone>(
    hm1: &mut FxHashMap<K, V>,
    hm2: &FxHashMap<K, V>,
    join: impl Fn(&mut V, &V) -> bool,
) -> bool {
    let mut changed = false;
    for (k, v) in hm2 {
        match hm1.entry(k.clone()) {
            Entry::Vacant(slot) => {
                slot.insert(v.clone());
                changed = true;
            }
            Entry::Occupied(mut entry) => {
                changed |= join(entry.get_mut(), v);
            }
        }
    }
    changed
}

pub type BodyAssignments = FxHashMap<Local, Vec<Location>>;

pub fn find_body_assignments(body: &Body<'_>) -> BodyAssignments {
    body.all_locations()
        .filter_map(|location| match body.stmt_at(location) {
            Either::Left(Statement {
                kind: StatementKind::Assign(box (lhs, _)),
                ..
            }) => Some((lhs.as_local()?, location)),
            Either::Right(Terminator {
                kind: TerminatorKind::Call { destination, .. },
                ..
            }) => Some((destination.as_local()?, location)),
            _ => None,
        })
        .into_group_map()
        .into_iter()
        .collect()
}

pub fn ty_resolve<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    match ty.kind() {
        TyKind::Alias(AliasKind::Opaque, alias_ty) => tcx.type_of(alias_ty.def_id).skip_binder(),
        _ => ty,
    }
}

pub fn manufacture_substs_for<'tcx>(
    tcx: TyCtxt<'tcx>,
    function: LocalDefId,
) -> Result<&'tcx List<GenericArg<'tcx>>, ErrorGuaranteed> {
    use rustc_middle::ty::{
        Binder, BoundRegionKind, DynKind, ExistentialPredicate, ExistentialProjection,
        ExistentialTraitRef, GenericParamDefKind, ImplPolarity, ParamTy, Region, TraitPredicate,
    };

    let generics = tcx.generics_of(function);
    let predicates = tcx.predicates_of(function).instantiate_identity(tcx);
    let types = (0..generics.count()).map(|gidx| {
        let param = generics.param_at(gidx, tcx);
        if let Some(default_val) = param.default_value(tcx) {
            return Ok(default_val.instantiate_identity());
        }
        match param.kind {
            // I'm not sure this is correct. We could probably return also "erased" or "static" here.
            GenericParamDefKind::Lifetime => {
                return Ok(GenericArg::from(Region::new_free(
                    tcx,
                    function.to_def_id(),
                    BoundRegionKind::BrAnon(None),
                )))
            }
            GenericParamDefKind::Const { .. } => {
                return Err(tcx.sess.span_err(
                    tcx.def_span(param.def_id),
                    "Cannot use constants as generic parameters in controllers",
                ))
            }
            GenericParamDefKind::Type { .. } => (),
        };

        let param_as_ty = ParamTy::for_def(param);
        let constraints = predicates.predicates.iter().filter_map(|clause| {
            let pred = if let Some(trait_ref) = clause.as_trait_clause() {
                if trait_ref.polarity() != ImplPolarity::Positive {
                    return None;
                };
                let Some(TraitPredicate { trait_ref, .. }) = trait_ref.no_bound_vars() else {
                    return Some(Err(tcx.sess.span_err(
                        tcx.def_span(param.def_id),
                        format!("Trait ref had binder {trait_ref:?}"),
                    )));
                };
                if !matches!(trait_ref.self_ty().kind(), TyKind::Param(p) if *p == param_as_ty) {
                    return None;
                };
                Some(ExistentialPredicate::Trait(
                    ExistentialTraitRef::erase_self_ty(tcx, trait_ref),
                ))
            } else if let Some(pred) = clause.as_projection_clause() {
                let pred = pred.no_bound_vars()?;
                if !matches!(pred.self_ty().kind(), TyKind::Param(p) if *p == param_as_ty) {
                    return None;
                };
                Some(ExistentialPredicate::Projection(
                    ExistentialProjection::erase_self_ty(tcx, pred),
                ))
            } else {
                None
            }?;

            Some(Ok(Binder::dummy(pred)))
        });
        let ty = Ty::new_dynamic(
            tcx,
            tcx.mk_poly_existential_predicates_from_iter(constraints)?,
            Region::new_free(tcx, function.to_def_id(), BoundRegionKind::BrAnon(None)),
            DynKind::Dyn,
        );
        Ok(GenericArg::from(ty))
    });
    tcx.mk_args_from_iter(types)
}
