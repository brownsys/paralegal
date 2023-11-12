use crate::{ast::Mutability, rust::hir::LanguageItems, ty};

pub trait APoorPersonsEquivalenceCheck {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool;
}

impl<T: APoorPersonsEquivalenceCheck> APoorPersonsEquivalenceCheck for ty::List<T> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .zip(other.iter())
                .all(|(left, right)| left.is_similar_enough(right, language_items))
    }
}

impl<'tcx> APoorPersonsEquivalenceCheck for ty::GenericArg<'tcx> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        use ty::GenericArgKind::*;
        match (self.unpack(), other.unpack()) {
            (Lifetime(_), Lifetime(_)) => true,
            (Type(t_a), Type(t_b)) => t_a.is_similar_enough(&t_b, language_items),
            (Const(c_1), Const(c_2)) => c_1.is_similar_enough(&c_2, language_items),
            _ => false,
        }
    }
}

impl<'tcx> APoorPersonsEquivalenceCheck for ty::Const<'tcx> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        self.kind() == other.kind() && self.ty().is_similar_enough(&other.ty(), language_items)
    }
}

impl<'tcx, T: APoorPersonsEquivalenceCheck> APoorPersonsEquivalenceCheck for ty::Binder<'tcx, T> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        self.bound_vars() == other.bound_vars()
            && self
                .as_ref()
                .skip_binder()
                .is_similar_enough(other.as_ref().skip_binder(), language_items)
    }
}

impl<'tcx> APoorPersonsEquivalenceCheck for ty::FnSig<'tcx> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        self.inputs_and_output
            .is_similar_enough(other.inputs_and_output, language_items)
            && self.c_variadic == other.c_variadic
            && self.unsafety == other.unsafety
            && self.abi == other.abi
    }
}

impl<'tcx> APoorPersonsEquivalenceCheck for ty::ExistentialPredicate<'tcx> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        use ty::ExistentialPredicate::*;
        use ty::TermKind::*;
        match (self, other) {
            (Trait(t_1), Trait(t_2)) => {
                t_1.def_id == t_2.def_id && t_1.substs.is_similar_enough(t_2.substs, language_items)
            }
            (Projection(p_1), Projection(p_2)) => {
                p_1.def_id == p_2.def_id
                    && p_1.substs.is_similar_enough(p_2.substs, language_items)
                    && match (p_1.term.unpack(), p_2.term.unpack()) {
                        (Ty(t_1), Ty(t_2)) => t_1.is_similar_enough(&t_2, language_items),
                        (Const(c_1), Const(c_2)) => c_1.is_similar_enough(&c_2, language_items),
                        _ => false,
                    }
            }
            (AutoTrait(t_1), AutoTrait(t_2)) => t_1 == t_2,
            _ => false,
        }
    }
}

impl<'tcx> APoorPersonsEquivalenceCheck for ty::AliasTy<'tcx> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        self.def_id == other.def_id && self.substs.is_similar_enough(other.substs, language_items)
    }
}

impl<'a, T: APoorPersonsEquivalenceCheck> APoorPersonsEquivalenceCheck for &'a T {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        (*self).is_similar_enough(*other, language_items)
    }
}

impl<'tcx> APoorPersonsEquivalenceCheck for ty::Ty<'tcx> {
    fn is_similar_enough(&self, other: &Self, language_items: &LanguageItems) -> bool {
        use crate::rust::rustc_type_ir::sty::TyKind::*;

        match (self.kind(), other.kind()) {
            (Int(a_i), Int(b_i)) => a_i == b_i,
            (Uint(a_u), Uint(b_u)) => a_u == b_u,
            (Float(a_f), Float(b_f)) => a_f == b_f,
            (Adt(a_d, a_s), Adt(b_d, b_s)) => {
                a_d == b_d && a_s.is_similar_enough(b_s, language_items)
            }
            (Foreign(a_d), Foreign(b_d)) => a_d == b_d,
            // This is where it gets hacky, we will basically consider all arrays
            // and slices the same so long as the element type is the same,
            // regardless of length.
            //
            // In future this could be refined to properly consider subtyping
            // relations, but we don't know the "directionality" of the comparison
            // anyway so no point in trying right now.
            (Array(a_t, _) | Slice(a_t), Array(b_t, _) | Slice(b_t)) => {
                a_t.is_similar_enough(b_t, language_items)
            }
            (RawPtr(a_t), RawPtr(b_t)) => {
                a_t.mutbl == b_t.mutbl && a_t.ty.is_similar_enough(&b_t.ty, language_items)
            }
            // We will also ignore regions for now
            (Ref(_, a_t, a_m), Ref(_, b_t, b_m)) => {
                a_t.is_similar_enough(b_t, language_items) && a_m == b_m
            }
            (FnDef(a_d, a_s), FnDef(b_d, b_s)) => {
                a_d == b_d && a_s.is_similar_enough(b_s, language_items)
            }
            (FnPtr(a_s), FnPtr(b_s)) => a_s.is_similar_enough(b_s, language_items),
            // Ignoring regions again
            (Dynamic(a_p, _, a_repr), Dynamic(b_p, _, b_repr)) => {
                a_p.is_similar_enough(b_p, language_items) && a_repr == b_repr
            }
            (Closure(a_d, a_s), Closure(b_d, b_s)) => {
                a_d == b_d && a_s.is_similar_enough(b_s, language_items)
            }
            (Generator(a_d, a_s, a_m), Generator(b_d, b_s, b_m)) => {
                if a_d == b_d && a_s.is_similar_enough(b_s, language_items) && a_m == b_m {
                    true
                } else {
                    debug!("{a_d:?} {a_s:?} {a_m:?} != {b_d:?} {b_s:?} {b_m:?}");
                    false
                }
            }
            (GeneratorWitness(a_g), GeneratorWitness(b_g)) => {
                // for some reason `a_g.equiv(b_g)` doesn't resolve properly and
                // gives me a type error so I inlined its body instead.
                a_g.bound_vars() == b_g.bound_vars()
                    && a_g
                        .skip_binder()
                        .is_similar_enough(b_g.skip_binder(), language_items)
            }
            (GeneratorWitnessMIR(a_d, a_s), GeneratorWitnessMIR(b_d, b_s)) => {
                a_d == b_d && a_s.is_similar_enough(b_s, language_items)
            }
            (Tuple(a_t), Tuple(b_t)) => a_t.is_similar_enough(b_t, language_items),
            (Alias(a_i, a_p), Alias(b_i, b_p)) => {
                a_i == b_i && a_p.is_similar_enough(b_p, language_items)
            }
            //(Param(a_p), Param(b_p)) => a_p == b_p,

            // We try to substitute parameters but sometimes they stick around
            // and Justus is not sure why. So we just skip comparison if one is
            // a parameter
            (Param(_), _) | (_, Param(_)) => true,
            (Bound(a_d, a_b), Bound(b_d, b_b)) => a_d == b_d && a_b == b_b,
            (Placeholder(a_p), Placeholder(b_p)) => a_p == b_p,
            (Infer(a_t), Infer(b_t)) => a_t == b_t,
            (Error(a_e), Error(b_e)) => a_e == b_e,
            (Bool, Bool) | (Char, Char) | (Str, Str) | (Never, Never) => true,
            (Adt(a, _), Ref(_, b, Mutability::Mut)) | (Ref(_, b, Mutability::Mut), Adt(a, _))
                if Some(a.did()) == language_items.resume_ty() =>
            {
                matches!(b.kind(), Adt(c, _) if Some(c.did()) == language_items.context())
            }
            // This is created when certain async functions are called. We could
            // additionally check that the input and output types match but I'm
            // lazy atm.
            (Dynamic(bound_predicate, _, _), Generator(_, _, _))
            | (Generator(_, _, _), Dynamic(bound_predicate, _, _)) => {
                debug!("Testing {self:?} and {other:?}\n  {bound_predicate:?}");
                matches!(
                    bound_predicate.first(),
                    Some(predicate)
                    if matches!(
                        predicate.skip_binder(),
                        ty::ExistentialPredicate::Trait(trait_predicate)
                        if Some(trait_predicate.def_id) == language_items.future_trait()
                    )
                )
            }
            // This is created by the `vec` macro when it uses `ShallowInitBox`
            (RawPtr(t_and_mut), _) | (_, RawPtr(t_and_mut))
                if t_and_mut.mutbl.is_mut()
                    && t_and_mut.ty.kind() == &ty::TyKind::Uint(ty::UintTy::U8) =>
            {
                self.is_box() && self.boxed_ty().is_array()
                    || other.is_box() && other.boxed_ty().is_array()
            }
            _ => false,
        }
    }
}
