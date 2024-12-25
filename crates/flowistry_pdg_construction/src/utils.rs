use std::{collections::hash_map::Entry, hash::Hash};

use either::Either;

use itertools::Itertools;
use log::trace;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{def_id::DefId, Defaultness};
use rustc_middle::{
    mir::{
        tcx::PlaceTy, Body, HasLocalDecls, Local, Location, Operand, Place, ProjectionElem,
        Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{
        AssocItemContainer, Binder, EarlyBinder, GenericArg, GenericArgsRef, Instance,
        InstanceKind, Region, Ty, TyCtxt, TyKind, TypingEnv,
    },
};
use rustc_span::{source_map::Spanned, ErrorGuaranteed, Span};
use rustc_type_ir::{fold::TypeFoldable, AliasTyKind, PredicatePolarity, RegionKind};
use rustc_utils::{BodyExt, PlaceExt};

pub trait Captures<'a> {}
impl<T: ?Sized> Captures<'_> for T {}

/// An async check that does not crash if called on closures.
pub fn is_async(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    !tcx.is_closure_like(def_id) && tcx.asyncness(def_id).is_async()
}

pub type ArgSlice<'a, 'tcx> = &'a [Spanned<Operand<'tcx>>];

/// Resolve the `def_id` item to an instance.
pub fn try_resolve_function<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    typing_env: TypingEnv<'tcx>,
    args: GenericArgsRef<'tcx>,
) -> Option<Instance<'tcx>> {
    let typing_env = typing_env.with_post_analysis_normalized(tcx);
    Instance::try_resolve(tcx, typing_env, def_id, args).unwrap()
}

/// Returns whether this method is expected to have a body we can analyze.
///
/// Specifically this returns `true` if `function` refers to an associated item
/// of a trait which has *no* default value.
///
/// Note: While you are supposed to call this whit a `function` that refers to a
/// function, it will not crash if it refers to a type or constant instead.
pub fn is_virtual(tcx: TyCtxt, function: DefId) -> bool {
    tcx.opt_associated_item(function).is_some_and(|assoc_item| {
        matches!(
            assoc_item.container,
            AssocItemContainer::Trait
            if !matches!(
                assoc_item.defaultness(tcx),
                Defaultness::Default { has_value: true })
        )
    })
}

/// The "canonical" way we monomorphize
pub fn try_monomorphize<'tcx, 'a, T>(
    inst: Instance<'tcx>,
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    t: &'a T,
    span: Span,
) -> Result<T, ErrorGuaranteed>
where
    T: TypeFoldable<TyCtxt<'tcx>> + Clone + std::fmt::Debug,
{
    inst.try_instantiate_mir_and_normalize_erasing_regions(
        tcx,
        typing_env,
        EarlyBinder::bind(tcx.erase_regions(t.clone())),
    )
    .map_err(|e| {
        tcx.dcx().span_err(
            span,
            format!("failed to monomorphize with instance {inst:?} due to {e:?}"),
        )
    })
}

/// Attempt to interpret this type as a statically determinable function and its
/// generic arguments.
pub fn type_as_fn<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let ty = ty_resolve(ty, tcx);
    match ty.kind() {
        TyKind::FnDef(def_id, generic_args)
        | TyKind::Coroutine(def_id, generic_args)
        | TyKind::Closure(def_id, generic_args) => Some((*def_id, generic_args)),
        ty => {
            trace!("Bailing from handle_call because func is literal with type: {ty:?}");
            None
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
            &elem,
            |_, field, _| match ty.ty.kind() {
                TyKind::Closure(_, args) => {
                    let upvar_tys = args.as_closure().upvar_tys();
                    upvar_tys.iter().nth(field.as_usize()).unwrap()
                }
                TyKind::Coroutine(_, args) => {
                    let upvar_tys = args.as_coroutine().upvar_tys();
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
        TyKind::Alias(AliasTyKind::Opaque, alias_ty) => tcx.type_of(alias_ty.def_id).skip_binder(),
        _ => ty,
    }
}

pub fn manufacture_substs_for(
    tcx: TyCtxt<'_>,
    function: DefId,
) -> Result<GenericArgsRef<'_>, ErrorGuaranteed> {
    use rustc_middle::ty::{
        DynKind, ExistentialPredicate, ExistentialProjection, ExistentialTraitRef,
        GenericParamDefKind, ParamTy, TraitPredicate,
    };

    trace!("Manufacturing for {function:?}");

    let generics = tcx.generics_of(function);
    trace!("Found generics {generics:?}");
    let predicates = tcx.predicates_of(function).instantiate_identity(tcx);
    trace!("Found predicates {predicates:?}");
    let lang_items = tcx.lang_items();
    let types = (0..generics.count()).map(|gidx| {
        let param = generics.param_at(gidx, tcx);
        if let Some(default_val) = param.default_value(tcx) {
            return Ok(default_val.instantiate_identity());
        }
        match param.kind {
            // I'm not sure this is correct. We could probably return also "erased" or "static" here.
            GenericParamDefKind::Lifetime => {
                return Ok(GenericArg::from(Region::new_from_kind(
                    tcx,
                    RegionKind::ReErased,
                )))
            }
            GenericParamDefKind::Const { .. } => {
                return Err(tcx.dcx().span_err(
                    tcx.def_span(param.def_id),
                    "Cannot use constants as generic parameters in controllers",
                ))
            }
            GenericParamDefKind::Type { .. } => (),
        };

        let param_as_ty = ParamTy::for_def(param);
        let constraints = predicates.predicates.iter().filter_map(|clause| {
            let pred = if let Some(trait_ref) = clause.as_trait_clause() {
                if trait_ref.polarity() != PredicatePolarity::Positive {
                    return None;
                };
                let Some(TraitPredicate { trait_ref, .. }) = trait_ref.no_bound_vars() else {
                    return Some(Err(tcx.dcx().span_err(
                        tcx.def_span(param.def_id),
                        format!("Trait ref had binder {trait_ref:?}"),
                    )));
                };
                if !matches!(trait_ref.self_ty().kind(), TyKind::Param(p) if *p == param_as_ty) {
                    return None;
                };
                if Some(trait_ref.def_id) == lang_items.sized_trait()
                    || tcx.trait_is_auto(trait_ref.def_id)
                {
                    trace!("    bailing because trait is auto trait");
                    return None;
                }
                Some(ExistentialPredicate::Trait(
                    ExistentialTraitRef::erase_self_ty(tcx, trait_ref),
                ))
            } else if let Some(pred) = clause.as_projection_clause() {
                trace!("    is projection clause");
                let Some(pred) = pred.no_bound_vars() else {
                    return Some(Err(tcx.dcx().span_err(
                        tcx.def_span(param.def_id),
                        "Predicate has a bound variable",
                    )));
                };
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
        let mut predicates = constraints.collect::<Result<Vec<_>, _>>()?;
        trace!("  collected predicates {predicates:?}");
        let no_args: [GenericArg; 0] = [];
        match predicates.len() {
            0 => predicates.push(Binder::dummy(ExistentialPredicate::Trait(
                ExistentialTraitRef::new(
                    tcx,
                    tcx.get_diagnostic_item(rustc_span::sym::Any)
                        .expect("The `Any` item is not defined."),
                    no_args,
                ),
            ))),
            1 => (),
            _ => {
                return Err(tcx.dcx().span_err(
                    tcx.def_span(param.def_id),
                    format!(
                        "can only synthesize a trait object for one non-auto trait, got {}",
                        predicates.len()
                    ),
                ));
            }
        };
        let poly_predicate = tcx.mk_poly_existential_predicates_from_iter(predicates.into_iter());
        trace!("  poly predicate {poly_predicate:?}");
        let ty = Ty::new_dynamic(
            tcx,
            poly_predicate,
            Region::new_from_kind(tcx, RegionKind::ReErased),
            DynKind::Dyn,
        );
        Ok(GenericArg::from(ty))
    });
    tcx.mk_args_from_iter(types)
}

#[derive(Clone, Copy, Debug, strum::AsRefStr)]
#[strum(serialize_all = "kebab-case")]
pub enum ShimType {
    Once,
    FnPtr,
}

pub fn handle_shims<'tcx>(
    resolved_fn: Instance<'tcx>,
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    span: Span,
) -> Option<(Instance<'tcx>, ShimType)> {
    match resolved_fn.def {
        InstanceKind::ClosureOnceShim { .. } => {
            // Rustc has inserted a call to the shim that maps `Fn` and `FnMut`
            // instances to an `FnOnce`. This shim has no body itself so we
            // can't just inline, we must explicitly simulate it's effects by
            // changing the target function and by setting the calling
            // convention to that of a shim.

            // Because this is a well defined internal item we can make
            // assumptions about its generic arguments.
            let Some((func_a, _rest)) = resolved_fn.args.split_first() else {
                unreachable!()
            };
            let Some((func_t, g)) = type_as_fn(tcx, func_a.expect_ty()) else {
                unreachable!()
            };
            let instance = Instance::expect_resolve(tcx, typing_env, func_t, g, span);
            Some((instance, ShimType::Once))
        }
        InstanceKind::FnPtrShim { .. } => {
            let Some((func_a, _rest)) = resolved_fn.args.split_first() else {
                unreachable!()
            };
            let Some((func_t, g)) = type_as_fn(tcx, func_a.expect_ty()) else {
                unreachable!()
            };
            let instance = Instance::expect_resolve(tcx, typing_env, func_t, g, span);

            Some((instance, ShimType::FnPtr))
        }
        _ => None,
    }
}
