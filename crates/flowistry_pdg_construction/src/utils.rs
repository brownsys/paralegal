use std::{collections::hash_map::Entry, hash::Hash};

use either::Either;

use itertools::Itertools;
use log::trace;

use rustc_borrowck::consumers::PlaceConflictBias;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{self as hir, def_id::DefId, Defaultness};
use rustc_middle::{
    mir::{
        tcx::PlaceTy, Body, HasLocalDecls, Local, Location, Operand, Place, PlaceElem, PlaceRef,
        ProjectionElem, Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{
        self, AssocItemContainer, Binder, EarlyBinder, GenericArg, GenericArgsRef, Instance,
        InstanceKind, Region, Ty, TyCtxt, TyKind, TypeVisitable, TypeVisitor, TypingEnv,
    },
};
use rustc_span::{source_map::Spanned, ErrorGuaranteed, Span};
use rustc_type_ir::{fold::TypeFoldable, AliasTyKind, PredicatePolarity, RegionKind};
use rustc_utils::{BodyExt, PlaceExt};

/// An async check that does not crash if called on closures.
pub fn is_async(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    !tcx.is_closure_like(def_id) && !tcx.is_constructor(def_id) && tcx.asyncness(def_id).is_async()
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

pub fn place_ty_eq<'tcx>(a: PlaceTy<'tcx>, b: PlaceTy<'tcx>) -> bool {
    a.ty == b.ty && a.variant_index == b.variant_index
}

/// Returns whether this method is expected to have a body we can analyze.
///
/// Specifically this returns `true` if `function` refers to an associated item
/// of a trait which has *no* default value.
///
/// Note: While you are supposed to call this with a `function` that refers to a
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

pub enum TyAsFnResult<'tcx> {
    Resolved {
        def_id: DefId,
        generic_args: GenericArgsRef<'tcx>,
    },
    FnPtr,
    NotAFunction,
}

impl<'tcx> TyAsFnResult<'tcx> {
    pub fn unwrap(self) -> (DefId, GenericArgsRef<'tcx>) {
        match self {
            TyAsFnResult::Resolved {
                def_id,
                generic_args,
            } => (def_id, generic_args),
            TyAsFnResult::FnPtr => panic!("Expected a static function, but got a function pointer"),
            TyAsFnResult::NotAFunction => panic!("Expected a function, but got something else"),
        }
    }

    pub fn to_option(self) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        match self {
            TyAsFnResult::Resolved {
                def_id,
                generic_args,
            } => Some((def_id, generic_args)),
            TyAsFnResult::FnPtr | TyAsFnResult::NotAFunction => None,
        }
    }
}

/// Attempt to interpret this type as a statically determinable function and its
/// generic arguments.
pub fn type_as_fn<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> TyAsFnResult<'tcx> {
    let ty = ty_resolve(ty, tcx);
    match ty.kind() {
        TyKind::FnDef(def_id, generic_args)
        | TyKind::Coroutine(def_id, generic_args)
        | TyKind::Closure(def_id, generic_args) => TyAsFnResult::Resolved {
            def_id: *def_id,
            generic_args,
        },
        TyKind::FnPtr(..) => TyAsFnResult::FnPtr,
        ty => {
            trace!("Bailing from handle_call because func is literal with type: {ty:?}");
            TyAsFnResult::NotAFunction
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

pub enum ShimResult<'tcx> {
    IsHandledShim {
        instance: Instance<'tcx>,
        shim_type: ShimType,
    },
    IsNonHandleableShim,
    IsNotShim,
}

pub fn handle_shims<'tcx>(
    resolved_fn: Instance<'tcx>,
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    span: Span,
) -> ShimResult<'tcx> {
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
            let (func_t, g) = match type_as_fn(tcx, func_a.expect_ty()) {
                TyAsFnResult::Resolved {
                    def_id,
                    generic_args,
                } => (def_id, generic_args),
                TyAsFnResult::FnPtr => {
                    return ShimResult::IsNonHandleableShim;
                }
                TyAsFnResult::NotAFunction => {
                    unreachable!("Expected a function, but got something else");
                }
            };
            let instance = Instance::expect_resolve(tcx, typing_env, func_t, g, span);
            ShimResult::IsHandledShim {
                instance,
                shim_type: ShimType::Once,
            }
        }
        InstanceKind::FnPtrShim { .. } => {
            let Some((func_a, _rest)) = resolved_fn.args.split_first() else {
                unreachable!()
            };
            let (func_t, g) = match type_as_fn(tcx, func_a.expect_ty()) {
                TyAsFnResult::Resolved {
                    def_id,
                    generic_args,
                } => (def_id, generic_args),
                TyAsFnResult::FnPtr => {
                    return ShimResult::IsNonHandleableShim;
                }
                TyAsFnResult::NotAFunction => {
                    unreachable!("Expected a function, but got something else");
                }
            };
            let instance = Instance::expect_resolve(tcx, typing_env, func_t, g, span);
            ShimResult::IsHandledShim {
                instance,
                shim_type: ShimType::FnPtr,
            }
        }
        _ => ShimResult::IsNotShim,
    }
}

#[macro_export]
macro_rules! debug_assert_resolved {
    ($e:expr) => {
        #[cfg(debug_assertions)]
        {
            $crate::utils::assert_resolved(&$e, || {
                format!("Expected {:?} to have resolved type", $e)
            });
        }
    };
}

pub fn assert_resolved<'tcx>(rvalue: &impl TypeVisitable<TyCtxt<'tcx>>, msg: impl Fn() -> String) {
    struct V<M>(M);

    impl<'tcx, M: Fn() -> String> TypeVisitor<TyCtxt<'tcx>> for V<M> {
        fn visit_ty(&mut self, ty: Ty<'tcx>) -> () {
            match ty.kind() {
                TyKind::Alias(..) | TyKind::Param(_) => {
                    panic!("Found type variable {ty:?}: {}", (self.0)())
                }
                _ => (),
            }
        }
    }

    let mut v = V(msg);
    rvalue.visit_with(&mut v);
}

// #################################################################################################
// This is a copy of the code in rustc_borrowck::consumers::places_conflict, reproduced here to make
// slight alterations that do not throw an error for nested references
// #################################################################################################

/// Helper function for checking if places conflict with a mutable borrow and deep access depth.
/// This is used to check for places conflicting outside of the borrow checking code (such as in
/// dataflow).
pub fn places_conflict<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_place: Place<'tcx>,
    access_place: Place<'tcx>,
) -> bool {
    let borrow_local = borrow_place.local;
    let access_local = access_place.local;
    let access_place = access_place.as_ref();

    if borrow_local != access_local {
        // We have proven the borrow disjoint - further projections will remain disjoint.
        return false;
    }

    // This Local/Local case is handled by the more general code below, but
    // it's so common that it's a speed win to check for it first.
    if borrow_place.projection.is_empty() && access_place.projection.is_empty() {
        return true;
    }

    // loop invariant: borrow_c is always either equal to access_c or disjoint from it.
    for ((borrow_place, borrow_c), &access_c) in
        std::iter::zip(borrow_place.iter_projections(), access_place.projection)
    {
        // Borrow and access path both have more components.
        //
        // Examples:
        //
        // - borrow of `a.(...)`, access to `a.(...)`
        // - borrow of `a.(...)`, access to `b.(...)`
        //
        // Here we only see the components we have checked so
        // far (in our examples, just the first component). We
        // check whether the components being borrowed vs
        // accessed are disjoint (as in the second example,
        // but not the first).
        match place_projection_conflict(
            tcx,
            body,
            borrow_place,
            borrow_c,
            access_c,
            PlaceConflictBias::Overlap,
        ) {
            Overlap::Arbitrary => {
                // We have encountered different fields of potentially
                // the same union - the borrow now partially overlaps.
                //
                // There is no *easy* way of comparing the fields
                // further on, because they might have different types
                // (e.g., borrows of `u.a.0` and `u.b.y` where `.0` and
                // `.y` come from different structs).
                //
                // We could try to do some things here - e.g., count
                // dereferences - but that's probably not a good
                // idea, at least for now, so just give up and
                // report a conflict. This is unsafe code anyway so
                // the user could always use raw pointers.
                return true;
            }
            Overlap::EqualOrDisjoint => {
                // This is the recursive case - proceed to the next element.
            }
            Overlap::Disjoint => {
                // We have proven the borrow disjoint - further
                // projections will remain disjoint.
                return false;
            }
        }
    }

    if borrow_place.projection.len() > access_place.projection.len() {
        for (base, elem) in borrow_place
            .iter_projections()
            .skip(access_place.projection.len())
        {
            // Borrow path is longer than the access path. Examples:
            //
            // - borrow of `a.b.c`, access to `a.b`
            //
            // Here, we know that the borrow can access a part of
            // our place. This is a conflict if that is a part our
            // access cares about.

            let base_ty = base.ty(body, tcx).ty;

            match (elem, &base_ty.kind()) {
                (ProjectionElem::Deref, ty::Ref(_, _, hir::Mutability::Not)) => {
                    // This occurs only in two cases. Either we have a reference
                    // as an argument, which causes queries such as
                    // conflicting("(*_1)", "_2") or if we have a raw pointer in
                    // the mix. In the reference case the alias analysis will
                    // already keep track of the conflict. Raw pointers by
                    // themselves are not soundly supported. However this can
                    // also occur via a manual "deref" (or somesuch), on which
                    // case we rely on the lifetimes declared on those functions
                    // to be correct and then our alias analysis will pick it up
                    // correctly.
                    return false;
                }
                (ProjectionElem::Deref, _)
                | (ProjectionElem::Field { .. }, _)
                | (ProjectionElem::Index { .. }, _)
                | (ProjectionElem::ConstantIndex { .. }, _)
                | (ProjectionElem::Subslice { .. }, _)
                | (ProjectionElem::OpaqueCast { .. }, _)
                | (ProjectionElem::Subtype(_), _)
                | (ProjectionElem::Downcast { .. }, _) => {
                    // Recursive case. This can still be disjoint on a
                    // further iteration if this a shallow access and
                    // there's a deref later on, e.g., a borrow
                    // of `*x.y` while accessing `x`.
                }
            }
        }
    }

    true
}

#[derive(Clone, Copy)]
pub(crate) enum Overlap {
    Arbitrary,
    EqualOrDisjoint,
    Disjoint,
}

// Given that the bases of `elem1` and `elem2` are always either equal
// or disjoint (and have the same type!), return the overlap situation
// between `elem1` and `elem2`.
fn place_projection_conflict<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    pi1: PlaceRef<'tcx>,
    pi1_elem: PlaceElem<'tcx>,
    pi2_elem: PlaceElem<'tcx>,
    bias: PlaceConflictBias,
) -> Overlap {
    match (pi1_elem, pi2_elem) {
        (ProjectionElem::Deref, ProjectionElem::Deref) => {
            // derefs (e.g., `*x` vs. `*x`) - recur.
            Overlap::EqualOrDisjoint
        }
        (ProjectionElem::OpaqueCast(_), ProjectionElem::OpaqueCast(_)) => {
            // casts to other types may always conflict irrespective of the type being cast to.
            Overlap::EqualOrDisjoint
        }
        (ProjectionElem::Field(f1, _), ProjectionElem::Field(f2, _)) => {
            if f1 == f2 {
                // same field (e.g., `a.y` vs. `a.y`) - recur.
                Overlap::EqualOrDisjoint
            } else {
                let ty = pi1.ty(body, tcx).ty;
                if ty.is_union() {
                    // Different fields of a union, we are basically stuck.
                    Overlap::Arbitrary
                } else {
                    // Different fields of a struct (`a.x` vs. `a.y`). Disjoint!
                    Overlap::Disjoint
                }
            }
        }
        (ProjectionElem::Downcast(_, v1), ProjectionElem::Downcast(_, v2)) => {
            // different variants are treated as having disjoint fields,
            // even if they occupy the same "space", because it's
            // impossible for 2 variants of the same enum to exist
            // (and therefore, to be borrowed) at the same time.
            //
            // Note that this is different from unions - we *do* allow
            // this code to compile:
            //
            // ```
            // fn foo(x: &mut Result<i32, i32>) {
            //     let mut v = None;
            //     if let Ok(ref mut a) = *x {
            //         v = Some(a);
            //     }
            //     // here, you would *think* that the
            //     // *entirety* of `x` would be borrowed,
            //     // but in fact only the `Ok` variant is,
            //     // so the `Err` variant is *entirely free*:
            //     if let Err(ref mut a) = *x {
            //         v = Some(a);
            //     }
            //     drop(v);
            // }
            // ```
            if v1 == v2 {
                Overlap::EqualOrDisjoint
            } else {
                Overlap::Disjoint
            }
        }
        (
            ProjectionElem::Index(..),
            ProjectionElem::Index(..)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. },
        )
        | (
            ProjectionElem::ConstantIndex { .. } | ProjectionElem::Subslice { .. },
            ProjectionElem::Index(..),
        ) => {
            // Array indexes (`a[0]` vs. `a[i]`). These can either be disjoint
            // (if the indexes differ) or equal (if they are the same).
            match bias {
                PlaceConflictBias::Overlap => {
                    // If we are biased towards overlapping, then this is the recursive
                    // case that gives "equal *or* disjoint" its meaning.
                    Overlap::EqualOrDisjoint
                }
                PlaceConflictBias::NoOverlap => {
                    // If we are biased towards no overlapping, then this is disjoint.
                    Overlap::Disjoint
                }
            }
        }
        (
            ProjectionElem::ConstantIndex {
                offset: o1,
                min_length: _,
                from_end: false,
            },
            ProjectionElem::ConstantIndex {
                offset: o2,
                min_length: _,
                from_end: false,
            },
        )
        | (
            ProjectionElem::ConstantIndex {
                offset: o1,
                min_length: _,
                from_end: true,
            },
            ProjectionElem::ConstantIndex {
                offset: o2,
                min_length: _,
                from_end: true,
            },
        ) => {
            if o1 == o2 {
                Overlap::EqualOrDisjoint
            } else {
                Overlap::Disjoint
            }
        }
        (
            ProjectionElem::ConstantIndex {
                offset: offset_from_begin,
                min_length: min_length1,
                from_end: false,
            },
            ProjectionElem::ConstantIndex {
                offset: offset_from_end,
                min_length: min_length2,
                from_end: true,
            },
        )
        | (
            ProjectionElem::ConstantIndex {
                offset: offset_from_end,
                min_length: min_length1,
                from_end: true,
            },
            ProjectionElem::ConstantIndex {
                offset: offset_from_begin,
                min_length: min_length2,
                from_end: false,
            },
        ) => {
            // both patterns matched so it must be at least the greater of the two
            let min_length = std::cmp::max(min_length1, min_length2);
            // `offset_from_end` can be in range `[1..min_length]`, 1 indicates the last
            // element (like -1 in Python) and `min_length` the first.
            // Therefore, `min_length - offset_from_end` gives the minimal possible
            // offset from the beginning
            if offset_from_begin >= min_length - offset_from_end {
                Overlap::EqualOrDisjoint
            } else {
                Overlap::Disjoint
            }
        }
        (
            ProjectionElem::ConstantIndex {
                offset,
                min_length: _,
                from_end: false,
            },
            ProjectionElem::Subslice {
                from,
                to,
                from_end: false,
            },
        )
        | (
            ProjectionElem::Subslice {
                from,
                to,
                from_end: false,
            },
            ProjectionElem::ConstantIndex {
                offset,
                min_length: _,
                from_end: false,
            },
        ) => {
            if (from..to).contains(&offset) {
                Overlap::EqualOrDisjoint
            } else {
                Overlap::Disjoint
            }
        }
        (
            ProjectionElem::ConstantIndex {
                offset,
                min_length: _,
                from_end: false,
            },
            ProjectionElem::Subslice { from, .. },
        )
        | (
            ProjectionElem::Subslice { from, .. },
            ProjectionElem::ConstantIndex {
                offset,
                min_length: _,
                from_end: false,
            },
        ) => {
            if offset >= from {
                Overlap::EqualOrDisjoint
            } else {
                Overlap::Disjoint
            }
        }
        (
            ProjectionElem::ConstantIndex {
                offset,
                min_length: _,
                from_end: true,
            },
            ProjectionElem::Subslice {
                to, from_end: true, ..
            },
        )
        | (
            ProjectionElem::Subslice {
                to, from_end: true, ..
            },
            ProjectionElem::ConstantIndex {
                offset,
                min_length: _,
                from_end: true,
            },
        ) => {
            if offset > to {
                Overlap::EqualOrDisjoint
            } else {
                Overlap::Disjoint
            }
        }
        (
            ProjectionElem::Subslice {
                from: f1,
                to: t1,
                from_end: false,
            },
            ProjectionElem::Subslice {
                from: f2,
                to: t2,
                from_end: false,
            },
        ) => {
            if f2 >= t1 || f1 >= t2 {
                Overlap::Disjoint
            } else {
                Overlap::EqualOrDisjoint
            }
        }
        (ProjectionElem::Subslice { .. }, ProjectionElem::Subslice { .. }) => {
            Overlap::EqualOrDisjoint
        }
        (
            ProjectionElem::Deref
            | ProjectionElem::Field(..)
            | ProjectionElem::Index(..)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::OpaqueCast { .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::Subtype(_)
            | ProjectionElem::Downcast(..),
            _,
        ) => panic!(
            "mismatched projections in place_element_conflict: {:?} and {:?}",
            pi1_elem, pi2_elem
        ),
    }
}
