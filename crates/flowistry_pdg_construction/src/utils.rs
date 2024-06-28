use std::{collections::hash_map::Entry, fmt::Debug, hash::Hash};

use either::Either;

use itertools::Itertools;
use log::trace;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;

use rustc_middle::{
    mir::{
        tcx::PlaceTy, Body, HasLocalDecls, Local, Location, Place, ProjectionElem, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{
        self, Binder, BoundVariableKind, EarlyBinder, GenericArg, GenericArgKind, GenericArgsRef,
        Instance, List, ParamEnv, Region, Ty, TyCtxt, TyKind,
    },
};

use rustc_span::Span;
use rustc_type_ir::{fold::TypeFoldable, AliasKind};
use rustc_utils::{BodyExt, PlaceExt};

use crate::construct::Error;

pub trait Captures<'a> {}
impl<'a, T: ?Sized> Captures<'a> for T {}

/// An async check that does not crash if called on closures.
pub fn is_async(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    !tcx.is_closure(def_id) && tcx.asyncness(def_id).is_async()
}

/// Resolve the `def_id` item to an instance.
pub fn try_resolve_function<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    param_env: ParamEnv<'tcx>,
    args: GenericArgsRef<'tcx>,
) -> Option<Instance<'tcx>> {
    let param_env = param_env.with_reveal_all_normalized(tcx);
    Instance::resolve(tcx, param_env, def_id, args).unwrap()
}

/// Returns the default implementation of this method if it is a trait method.
pub fn is_non_default_trait_method(tcx: TyCtxt, function: DefId) -> Option<DefId> {
    let assoc_item = tcx.opt_associated_item(function)?;
    if assoc_item.container != ty::AssocItemContainer::TraitContainer
        || assoc_item.defaultness(tcx).has_value()
    {
        return None;
    }
    assoc_item.trait_item_def_id
}

/// The "canonical" way we monomorphize
pub fn try_monomorphize<'tcx, 'a, T>(
    inst: Instance<'tcx>,
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    t: &'a T,
    span: Span,
) -> Result<T, Error<'tcx>>
where
    T: TypeFoldable<TyCtxt<'tcx>> + Clone + Debug,
{
    inst.try_subst_mir_and_normalize_erasing_regions(
        tcx,
        param_env,
        EarlyBinder::bind(tcx.erase_regions(t.clone())),
    )
    .map_err(|e| Error::NormalizationError {
        instance: inst,
        span,
        error: format!("{e:?}"),
    })
}

/// Attempt to interpret this type as a statically determinable function and its
/// generic arguments.
pub fn type_as_fn<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let ty = ty_resolve(ty, tcx);
    match ty.kind() {
        TyKind::FnDef(def_id, generic_args) => Some((*def_id, generic_args)),
        TyKind::Generator(def_id, generic_args, _) => Some((*def_id, generic_args)),
        ty => {
            trace!("Bailing from handle_call because func is literal with type: {ty:?}");
            None
        }
    }
}

/// If `target_ty` is supplied checks that the final type is the same as `target_ty`.
pub(crate) fn retype_place<'tcx>(
    orig: Place<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    def_id: DefId,
    target_ty: Option<PlaceTy<'tcx>>,
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
            trace!("Breaking on param-like type {:?}", ty.ty);
            break;
        }

        // // Don't continue if we reach a private field
        // if let ProjectionElem::Field(field, _) = elem {
        //     if let Some(adt_def) = ty.ty.ty_adt_def() {
        //         let field = adt_def
        //             .all_fields()
        //             .nth(field.as_usize())
        //             .unwrap_or_else(|| {
        //                 panic!("ADT for {:?} does not have field {field:?}", ty.ty);
        //             });
        //         if !field.vis.is_accessible_from(def_id, tcx) {
        //             break;
        //         }
        //     }
        // }

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

    if let Some(target_ty) = target_ty {
        if !ty.equiv(&target_ty) {
            let p1_str = format!("{orig:?}");
            let p2_str = format!("{p:?}");
            let l = p1_str.len().max(p2_str.len());
            panic!("Retyping in {} failed to produce an equivalent type.\n  Src {p1_str:l$} : {target_ty:?}\n  Dst {p2_str:l$} : {ty:?}", tcx.def_path_str(def_id))
        }
    }

    trace!("    Final translation: {p:?}");
    p
}

pub trait SimpleTyEquiv {
    fn equiv(&self, other: &Self) -> bool;
}

impl<'tcx> SimpleTyEquiv for Ty<'tcx> {
    fn equiv(&self, other: &Self) -> bool {
        self.kind().equiv(other.kind())
    }
}

impl<'tcx, T: SimpleTyEquiv> SimpleTyEquiv for [T] {
    fn equiv(&self, other: &Self) -> bool {
        self.iter().zip(other.iter()).all(|(a, b)| a.equiv(b))
    }
}

impl<T: SimpleTyEquiv> SimpleTyEquiv for ty::List<T> {
    fn equiv(&self, other: &Self) -> bool {
        self.as_slice().equiv(other.as_slice())
    }
}

impl<'tcx> SimpleTyEquiv for GenericArg<'tcx> {
    fn equiv(&self, other: &Self) -> bool {
        match (&self.unpack(), &other.unpack()) {
            (GenericArgKind::Const(a), GenericArgKind::Const(b)) => a == b,
            (GenericArgKind::Lifetime(a), GenericArgKind::Lifetime(b)) => a.equiv(b),
            (GenericArgKind::Type(a), GenericArgKind::Type(b)) => a.equiv(b),
            _ => false,
        }
    }
}

impl<'tcx> SimpleTyEquiv for Region<'tcx> {
    fn equiv(&self, _other: &Self) -> bool {
        true
    }
}

impl<'tcx, T: SimpleTyEquiv> SimpleTyEquiv for ty::Binder<'tcx, T> {
    fn equiv(&self, other: &Self) -> bool {
        self.bound_vars().equiv(other.bound_vars())
            && self
                .as_ref()
                .skip_binder()
                .equiv(other.as_ref().skip_binder())
    }
}

impl SimpleTyEquiv for BoundVariableKind {
    fn equiv(&self, other: &Self) -> bool {
        self == other
    }
}

impl<'tcx> SimpleTyEquiv for ty::TypeAndMut<'tcx> {
    fn equiv(&self, other: &Self) -> bool {
        self.mutbl == other.mutbl && self.ty.equiv(&other.ty)
    }
}

impl<'tcx> SimpleTyEquiv for ty::FnSig<'tcx> {
    fn equiv(&self, other: &Self) -> bool {
        let Self {
            inputs_and_output,
            c_variadic,
            unsafety,
            abi,
        } = *self;
        inputs_and_output.equiv(other.inputs_and_output)
            && c_variadic == other.c_variadic
            && unsafety == other.unsafety
            && abi == other.abi
    }
}

impl<T: SimpleTyEquiv + ?Sized> SimpleTyEquiv for &T {
    fn equiv(&self, other: &Self) -> bool {
        (*self).equiv(*other)
    }
}

impl<'tcx> SimpleTyEquiv for ty::AliasTy<'tcx> {
    fn equiv(&self, other: &Self) -> bool {
        self.def_id == other.def_id && self.args.equiv(other.args)
    }
}

impl<'tcx> SimpleTyEquiv for ty::ExistentialPredicate<'tcx> {
    fn equiv(&self, other: &Self) -> bool {
        self == other
    }
}

fn is_wildcard(t: &TyKind<'_>) -> bool {
    matches!(
        t,
        TyKind::Param(..) | TyKind::Alias(..) | TyKind::Bound(..) | TyKind::Placeholder(..)
    ) || matches!(t,
        TyKind::Dynamic(pred, _, _) if matches!(
            pred.first().copied().and_then(Binder::no_bound_vars),
            Some(ty::ExistentialPredicate::Trait(tref))
            if tref.def_id == ty::tls::with(|tcx| tcx
                .get_diagnostic_item(rustc_span::sym::Any)
                .expect("The `Any` item is not defined."))
        )
    )
}

impl<'tcx> SimpleTyEquiv for TyKind<'tcx> {
    fn equiv(&self, other: &Self) -> bool {
        use rustc_type_ir::TyKind::*;
        match (self, other) {
            _ if is_wildcard(self) || is_wildcard(other) => true,
            (Int(a_i), Int(b_i)) => a_i == b_i,
            (Uint(a_u), Uint(b_u)) => a_u == b_u,
            (Float(a_f), Float(b_f)) => a_f == b_f,
            (Adt(a_d, a_s), Adt(b_d, b_s)) => a_d == b_d && a_s.equiv(b_s),
            (Foreign(a_d), Foreign(b_d)) => a_d == b_d,
            (Array(a_t, a_c), Array(b_t, b_c)) => a_t.equiv(b_t) && a_c == b_c,
            (Slice(a_t), Slice(b_t)) => a_t.equiv(b_t),
            (RawPtr(a_t), RawPtr(b_t)) => a_t.equiv(b_t),
            (Ref(a_r, a_t, a_m), Ref(b_r, b_t, b_m)) => {
                a_r.equiv(b_r) && a_t.equiv(b_t) && a_m == b_m
            }
            (FnDef(a_d, a_s), FnDef(b_d, b_s)) => a_d == b_d && a_s.equiv(b_s),
            (FnPtr(a_s), FnPtr(b_s)) => a_s.equiv(b_s),
            (Dynamic(a_p, a_r, a_repr), Dynamic(b_p, b_r, b_repr)) => {
                a_p.equiv(b_p) && a_r.equiv(b_r) && a_repr == b_repr
            }
            (Closure(a_d, a_s), Closure(b_d, b_s)) => a_d == b_d && a_s.equiv(b_s),
            (Generator(a_d, a_s, a_m), Generator(b_d, b_s, b_m)) => {
                a_d == b_d && a_s.equiv(b_s) && a_m == b_m
            }
            (GeneratorWitness(a_g), GeneratorWitness(b_g)) => a_g.equiv(b_g),
            (GeneratorWitnessMIR(a_d, a_s), GeneratorWitnessMIR(b_d, b_s)) => {
                a_d == b_d && a_s.equiv(b_s)
            }
            (Tuple(a_t), Tuple(b_t)) => a_t.equiv(b_t),
            (Alias(a_i, a_p), Alias(b_i, b_p)) => a_i == b_i && a_p.equiv(b_p),
            (Param(a_p), Param(b_p)) => a_p == b_p,
            (Bound(a_d, a_b), Bound(b_d, b_b)) => a_d == b_d && a_b == b_b,
            (Placeholder(a_p), Placeholder(b_p)) => a_p == b_p,
            (Infer(_a_t), Infer(_b_t)) => unreachable!(),
            (Error(a_e), Error(b_e)) => a_e == b_e,
            (Bool, Bool) | (Char, Char) | (Str, Str) | (Never, Never) => true,
            _ => false,
        }
    }
}

impl<'tcx> SimpleTyEquiv for PlaceTy<'tcx> {
    fn equiv(&self, other: &Self) -> bool {
        self.variant_index == other.variant_index && self.ty.equiv(&other.ty)
    }
}

pub(crate) fn hashset_join<T: Hash + Eq + PartialEq + Clone>(
    hs1: &mut FxHashSet<T>,
    hs2: &FxHashSet<T>,
) -> bool {
    let orig_len = hs1.len();
    hs1.extend(hs2.iter().cloned());
    hs1.len() != orig_len
}

pub(crate) fn hashmap_join<K: Hash + Eq + PartialEq + Clone, V: Clone>(
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

pub(crate) type BodyAssignments = FxHashMap<Local, Vec<Location>>;

pub(crate) fn find_body_assignments(body: &Body<'_>) -> BodyAssignments {
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

/// Resolve through type aliases
pub fn ty_resolve<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    match ty.kind() {
        TyKind::Alias(AliasKind::Opaque, alias_ty) => tcx.type_of(alias_ty.def_id).skip_binder(),
        _ => ty,
    }
}

/// This function creates dynamic types that satisfy the constraints on the
/// given function. It returns a list of generic arguments that are suitable for
/// calling `Instance::resolve` for this function, guaranteeing that the resolve
/// call does not fail.
///
/// This is achieved by constructing `dyn` types which assume the constraints of
/// the `where` clause for this function (and any parents).
pub fn manufacture_substs_for(
    tcx: TyCtxt<'_>,
    function: DefId,
) -> Result<&List<GenericArg<'_>>, Error> {
    use rustc_middle::ty::{
        Binder, BoundRegionKind, DynKind, ExistentialPredicate, ExistentialProjection,
        ExistentialTraitRef, GenericParamDefKind, ImplPolarity, ParamTy, Region, TraitPredicate,
    };

    trace!("Manufacturing for {function:?}");

    let generics = tcx.generics_of(function);
    trace!("Found generics {generics:?}");
    let predicates = tcx.predicates_of(function).instantiate_identity(tcx);
    trace!("Found predicates {predicates:?}");
    let lang_items = tcx.lang_items();
    let types = (0..generics.count()).map(|gidx| {
        let param = generics.param_at(gidx, tcx);
        trace!("Trying param {param:?}");
        if let Some(default_val) = param.default_value(tcx) {
            return Ok(default_val.instantiate_identity());
        }
        match param.kind {
            // I'm not sure this is correct. We could probably return also "erased" or "static" here.
            GenericParamDefKind::Lifetime => {
                return Ok(GenericArg::from(Region::new_free(
                    tcx,
                    function,
                    BoundRegionKind::BrAnon(None),
                )))
            }
            GenericParamDefKind::Const { .. } => {
                return Err(Error::ConstantInGenerics { function });
            }
            GenericParamDefKind::Type { .. } => (),
        };

        let param_as_ty = ParamTy::for_def(param);
        let constraints = predicates.predicates.iter().enumerate().rev().filter_map(
            |(_pidx, clause)| {
                trace!("  Trying clause {clause:?}");
                let pred = if let Some(trait_ref) = clause.as_trait_clause() {
                    trace!("    is trait clause");
                    if trait_ref.polarity() != ImplPolarity::Positive {
                        trace!("    Bailing because it is negative");
                        return None;
                    };
                    let Some(TraitPredicate { trait_ref, .. }) = trait_ref.no_bound_vars() else {
                        return Some(Err(Error::TraitRefWithBinder { function }));
                    };
                    if !matches!(trait_ref.self_ty().kind(), TyKind::Param(p) if *p == param_as_ty)
                    {
                        trace!("    Bailing because self type is not param type");
                        return None;
                    };
                    if Some(trait_ref.def_id) == lang_items.sized_trait()
                        || tcx.trait_is_auto(trait_ref.def_id)
                    {
                        trace!("    bailing because trait is auto trait");
                        return None;
                    }
                    ExistentialPredicate::Trait(ExistentialTraitRef::erase_self_ty(tcx, trait_ref))
                } else if let Some(pred) = clause.as_projection_clause() {
                    trace!("    is projection clause");
                    let Some(pred) = pred.no_bound_vars() else {
                        return Some(Err(Error::BoundVariablesInPredicates { function }));
                    };
                    if !matches!(pred.self_ty().kind(), TyKind::Param(p) if *p == param_as_ty) {
                        trace!("    Bailing because self type is not param type");
                        return None;
                    };
                    ExistentialPredicate::Projection(ExistentialProjection::erase_self_ty(
                        tcx, pred,
                    ))
                } else {
                    trace!("    is other clause: ignoring");
                    return None;
                };

                trace!("    Created predicate {pred:?}");

                Some(Ok(Binder::dummy(pred)))
            },
        );
        let mut predicates = constraints.collect::<Result<Vec<_>, _>>()?;
        trace!("  collected predicates {predicates:?}");
        match predicates.len() {
            0 => predicates.push(Binder::dummy(ExistentialPredicate::Trait(
                ExistentialTraitRef {
                    def_id: tcx
                        .get_diagnostic_item(rustc_span::sym::Any)
                        .expect("The `Any` item is not defined."),
                    args: List::empty(),
                },
            ))),
            1 => (),
            _ => {
                return Err(Error::TooManyPredicatesForSynthesizingGenerics {
                    function,
                    number: predicates.len() as u32,
                })
            }
        };
        let poly_predicate = tcx.mk_poly_existential_predicates_from_iter(predicates.into_iter());
        trace!("  poly predicate {poly_predicate:?}");
        let ty = Ty::new_dynamic(
            tcx,
            poly_predicate,
            Region::new_free(tcx, function, BoundRegionKind::BrAnon(None)),
            DynKind::Dyn,
        );
        trace!("  Created a dyn {ty:?}");
        Ok(GenericArg::from(ty))
    });
    let args = tcx.mk_args_from_iter(types)?;
    trace!("Created args {args:?}");
    Ok(args)
}
