use std::fmt::Display;

use crate::{ana::inline::GlobalLocal, mir, utils::DisplayViaDebug, Symbol};
use std::hash::Hash;

pub type VariantIdx = usize;

/// An operator in the projection algebra.
#[derive(Clone, Eq, Hash, Debug, Copy, PartialEq)]
pub enum Operator<F: Copy> {
    RefOf,
    DerefOf,
    MemberOf(F),
    ContainsAt(F),
    IndexOf,
    ArrayWith,
    Downcast(VariantIdx),
    Upcast(VariantIdx),
    Unknown,
}

/// Relationship of two [`Operator`]s. Used in [`Operator::cancel`].
#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy)]
pub enum Cancel<F> {
    /// Both operators were field-related but did not reference the same field
    NonOverlappingField(F, F),
    /// Both operators were variant cast related but did not reference the same variant
    NonOverlappingVariant(VariantIdx, VariantIdx),
    /// The operators canceled
    CancelBoth,
    CancelOne,
    /// The operators did not cancel
    Remains,
    Invalid,
}

impl<F: Copy + std::fmt::Display> std::fmt::Display for Cancel<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Cancel::*;
        match self {
            NonOverlappingField(f1, f2) => write!(f, "f{f1} != f{f2}"),
            NonOverlappingVariant(v1, v2) => write!(f, "#{v1} != #{v2}"),
            CancelBoth => f.write_str("cancel both"),
            CancelOne => f.write_str("cancel one"),
            Remains => f.write_str("remains"),
            Invalid => f.write_str("invalid combination"),
        }
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub enum Simplified<F: Copy> {
    Yes,
    NonOverlapping,
    Invalid(Operator<F>, Operator<F>),
}

impl<F: Copy> Operator<F> {
    /// Each operator has a dual, this flips this operator to that respective dual.
    pub fn flip(self) -> Self {
        use Operator::*;
        match self {
            RefOf => DerefOf,
            DerefOf => RefOf,
            MemberOf(f) => ContainsAt(f),
            ContainsAt(f) => MemberOf(f),
            Downcast(v) => Upcast(v),
            Upcast(v) => Downcast(v),
            Unknown => Unknown,
            ArrayWith => IndexOf,
            IndexOf => ArrayWith,
        }
    }

    pub fn is_unknown(self) -> bool {
        matches!(self, Operator::Unknown)
    }

    /// Determine for two term segments whether they cancel each other (for
    /// instance `*&x => x`) or not. It also reports if the two segments do not
    /// unify, which can be the case for fields and variant casts.
    ///
    /// I've been thinking about this and I think for fields the order here
    /// might actually matter. (And I think it would still be reorder safe).
    /// Say you do `a.f = b.g`. This statement is perfectly valid and it makes
    /// sense. If you reorder it you get `a = { .f: b.g }` and that (currently)
    /// cancels with `NonOverlappingField` because you get `ContainsAt(.f,
    /// MemberOf(b, .g))`.
    ///
    /// In the opposite case you have something like `a = { g: b }.f` this is
    /// obviously nonsense and not present in surface syntax but can be the
    /// result of substitution for instance for `x.g = b; a = x.f`. There will
    /// probably be other equations that describe what happens at `x.f` but this
    /// particular one when substituted is obviously useless. However note the
    /// order here is different. This is `MemberOf(ContainsAt(.g, b), .f)`. This
    /// one should eliminate.
    ///
    /// I had one fear about this which is "what happens when you reorder to the
    /// other side, doesn't the order change from the first one to the second?"
    /// turns out its fine, because the reordering will flip both segments and
    /// thus maintain the order. This is why I think adding this is not just
    /// safe but actually more sound.
    pub fn cancel(self, other: Self) -> Cancel<F>
    where
        F: PartialEq,
    {
        use Operator::*;
        match (self, other) {
            (Unknown, Unknown) => Cancel::CancelOne,
            (Unknown, _) | (_, Unknown) => Cancel::Remains,
            (ContainsAt(f), MemberOf(g)) => {
                if f == g {
                    Cancel::CancelBoth
                } else {
                    Cancel::NonOverlappingField(f, g)
                }
            }
            (Upcast(v1), Downcast(v2)) => {
                if v1 == v2 {
                    Cancel::CancelBoth
                } else {
                    Cancel::NonOverlappingVariant(v1, v2)
                }
            }
            (RefOf, DerefOf) | (DerefOf, RefOf) | (ArrayWith, IndexOf) => Cancel::CancelBoth,
            _ if other.is_projecting() && !self.is_projecting() => Cancel::Invalid,
            _ => Cancel::Remains,
        }
    }

    pub fn is_wrapping(self) -> bool {
        use Operator::*;
        matches!(self, ArrayWith | Upcast(_) | ContainsAt(_) | RefOf)
    }

    pub fn is_projecting(self) -> bool {
        use Operator::*;
        matches!(self, IndexOf | DerefOf | MemberOf(_) | Downcast(_))
    }

    /// Apply a function to the field, creating a new operator
    pub fn map_field<F0: Copy, G: FnMut(F) -> F0>(self, mut g: G) -> Operator<F0> {
        use Operator::*;
        match self {
            RefOf => RefOf,
            DerefOf => DerefOf,
            MemberOf(f) => MemberOf(g(f)),
            ContainsAt(f) => ContainsAt(g(f)),
            Upcast(v) => Upcast(v),
            Downcast(v) => Downcast(v),
            Unknown => Unknown,
            IndexOf => IndexOf,
            ArrayWith => ArrayWith,
        }
    }
}

impl<F: Copy + std::fmt::Display> std::fmt::Display for Operator<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Write;
        use Operator::*;
        match self {
            RefOf => f.write_char('&'),
            DerefOf => f.write_char('*'),
            Unknown => f.write_char('?'),
            MemberOf(m) => write!(f, ".{m}"),
            ContainsAt(m) => write!(f, "@{m}"),
            Downcast(s) => write!(f, "#{s:?}"),
            Upcast(s) => write!(f, "^{s:?}"),
            IndexOf => f.write_str("$"),
            ArrayWith => f.write_str("[]"),
        }
    }
}

/// Terms in the projection algebra
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Term<B, F: Copy> {
    /// The base of the term
    pub base: B,
    /// Operators applied to the term in inside-out order.
    terms: Vec<Operator<F>>,
}

impl<B, F: Copy> Term<B, F> {
    pub fn terms_inside_out(&self) -> &[Operator<F>] {
        &self.terms
    }

    pub fn into_terms_inside_out(self) -> Vec<Operator<F>> {
        self.terms
    }

    pub fn is_base(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn new_base(base: B) -> Self {
        Term {
            base,
            terms: vec![],
        }
    }

    pub fn add_deref_of(mut self) -> Self {
        self.terms.push(Operator::DerefOf);
        self
    }

    pub fn add_ref_of(mut self) -> Self {
        self.terms.push(Operator::RefOf);
        self
    }

    pub fn add_member_of(mut self, field: F) -> Self {
        self.terms.push(Operator::MemberOf(field));
        self
    }

    pub fn add_contains_at(mut self, field: F) -> Self {
        self.terms.push(Operator::ContainsAt(field));
        self
    }

    pub fn add_downcast(mut self, _symbol: Option<Symbol>, idx: VariantIdx) -> Self {
        self.terms.push(Operator::Downcast(idx));
        self
    }

    pub fn add_upcast(mut self, _symbol: Option<Symbol>, idx: VariantIdx) -> Self {
        self.terms.push(Operator::Upcast(idx));
        self
    }

    pub fn add_unknown(mut self) -> Self {
        self.terms.push(Operator::Unknown);
        self
    }

    pub fn add_index_of(mut self) -> Self {
        self.terms.push(Operator::IndexOf);
        self
    }

    pub fn add_array_with(mut self) -> Self {
        self.terms.push(Operator::ArrayWith);
        self
    }

    pub fn add_elem(mut self, elem: Operator<F>) -> Self {
        self.terms.push(elem);
        self
    }

    pub fn extend<I: IntoIterator<Item = Operator<F>>>(mut self, others: I) -> Self {
        self.terms.extend(others);
        self
    }

    pub fn base(&self) -> &B {
        &self.base
    }

    pub fn sub(&mut self, other: Self) {
        let Self { base, mut terms } = other;
        self.base = base;
        terms.append(&mut self.terms);
        std::mem::swap(&mut self.terms, &mut terms)
    }
    pub fn replace_base<B0>(&self, base: B0) -> Term<B0, F> {
        Term {
            base,
            terms: self.terms.clone(),
        }
    }

    pub fn replace_fields<F0: Copy, G: FnMut(F) -> F0>(&self, mut g: G) -> Term<B, F0>
    where
        B: Clone,
    {
        Term {
            base: self.base.clone(),
            terms: self.terms.iter().map(|f| f.map_field(&mut g)).collect(),
        }
    }

    pub fn from_raw(base: B, terms: Vec<Operator<F>>) -> Self {
        Self { base, terms }
    }

    pub fn simplify(&mut self) -> Simplified<F>
    where
        F: Eq + Display,
        B: Display,
    {
        let l = self.terms.len();
        if l < 2 {
            return Simplified::Yes;
        }
        let mut overlapping = true;
        let old_terms = std::mem::replace(&mut self.terms, Vec::with_capacity(l));
        let mut it = old_terms.into_iter();
        let mut after_first_unknown = None;
        let mut after_last_unknown = None;
        self.terms.push(it.next().unwrap());
        while let Some(op) = it.next() {
            let Some(prior) = self.terms.last().copied() else {
                self.terms.push(op);
                continue;
            };
            match prior.cancel(op) {
                Cancel::NonOverlappingField(_f, _g) => {
                    overlapping = false;
                }
                Cancel::NonOverlappingVariant(_v1, _v2) => {
                    overlapping = false;
                }
                Cancel::CancelBoth => {
                    self.terms.pop();
                    continue;
                }
                Cancel::CancelOne => {
                    continue;
                }
                Cancel::Remains => (),
                Cancel::Invalid => {
                    self.terms.push(op);
                    self.terms.extend(it);
                    return Simplified::Invalid(prior, op);
                }
            }
            self.terms.push(op);
            if op.is_unknown() {
                let _ = if after_first_unknown.is_none() {
                    &mut after_first_unknown
                } else {
                    &mut after_last_unknown
                }
                .insert(self.terms.len());
            }
        }
        if let (Some(from), Some(to)) = (after_first_unknown, after_last_unknown) {
            vec_drop_range(&mut self.terms, from..to);
        }
        if overlapping {
            Simplified::Yes
        } else {
            Simplified::NonOverlapping
        }
    }
}

fn vec_drop_range<T>(v: &mut Vec<T>, r: std::ops::Range<usize>) {
    let ptr = v.as_mut_ptr();
    for i in r.clone() {
        unsafe { ptr.add(i).drop_in_place() }
    }
    unsafe {
        std::ptr::copy(ptr.add(r.end), ptr.add(r.start), v.len() - r.end);
        v.set_len(v.len() - r.len());
    }
}

pub fn display_term_pieces<F: Display + Copy, B: Display>(
    f: &mut std::fmt::Formatter<'_>,
    terms: &[Operator<F>],
    base: &B,
) -> std::fmt::Result {
    use std::fmt::Write;
    use Operator::*;
    for t in terms.iter().rev() {
        if !matches!(t, ContainsAt(..) | ArrayWith) {
            f.write_char('(')?;
        }
        match t {
            RefOf => f.write_char('&'),
            DerefOf => f.write_char('*'),
            ContainsAt(field) => write!(f, "{{ .{}: ", field),
            Upcast(s) => write!(f, "#{s} "),
            Unknown => f.write_char('?'),
            ArrayWith => f.write_char('['),
            _ => Ok(()),
        }?
    }
    write!(f, "{}", base)?;
    for t in terms.iter() {
        match t {
            MemberOf(field) => write!(f, ".{}", field),
            ContainsAt(_) => f.write_str(" }"),
            Downcast(s) => write!(f, " #{s}"),
            ArrayWith => f.write_char(']'),
            IndexOf => write!(f, "[]"),
            _ => Ok(()),
        }?;
        if !matches!(t, ContainsAt(..) | ArrayWith) {
            f.write_char(')')?;
        }
    }
    Ok(())
}

impl<B: Display, F: Display + Copy> Display for Term<B, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        display_term_pieces(f, &self.terms, &self.base)
    }
}

/// An equation in the algebra
#[derive(Clone, Debug)]
pub struct Equality<B, F: Copy> {
    lhs: Term<B, F>,
    rhs: Term<B, F>,
    /// Controls how sanity checks are performed. If it is a cast we only check
    /// that the wrappings can be applied to the types, but we don't check that
    /// the types are equal after applying the wrappings.
    is_cast: bool,
}

impl<B, F: Copy> Equality<B, F> {
    pub fn unchecked_new(lhs: Term<B, F>, rhs: Term<B, F>, is_cast: bool) -> Self {
        Self { rhs, lhs, is_cast }
    }

    pub fn new_cast(lhs: Term<B, F>, rhs: Term<B, F>) -> Self {
        Self {
            lhs,
            rhs,
            is_cast: true,
        }
    }

    pub fn is_cast(&self) -> bool {
        self.is_cast
    }

    pub fn lhs(&self) -> &Term<B, F> {
        &self.lhs
    }

    pub fn rhs(&self) -> &Term<B, F> {
        &self.rhs
    }

    pub fn decompose(self) -> (Term<B, F>, Term<B, F>) {
        (self.lhs, self.rhs)
    }

    pub fn unsafe_refs(&mut self) -> [&mut Term<B, F>; 2] {
        [&mut self.lhs, &mut self.rhs]
    }

    /// Rearrange the equation, moving all operators from the left hand side to
    /// the right hand side term, [`Operator::flip`]ing them in the process.
    ///
    /// After calling this function it is guaranteed that `self.lhs.is_base() == true`
    ///
    /// If you want to rearrange from right to left use [`Equality::swap`]
    pub fn rearrange_left_to_right(&mut self) {
        self.rhs
            .terms
            .extend(self.lhs.terms.drain(..).rev().map(Operator::flip));
        assert!(self.lhs.terms.is_empty());
    }

    /// Swap the left and right hand side terms
    pub fn swap(&mut self) {
        std::mem::swap(&mut self.lhs, &mut self.rhs)
    }

    pub fn bases(&self) -> [&B; 2] {
        [self.lhs.base(), self.rhs.base()]
    }

    /// Apply a function to each base, creating a new equation with a
    /// potentially different base type.
    pub fn map_bases<B0, G: FnMut(&B) -> B0>(&self, mut f: G) -> Equality<B0, F> {
        Equality {
            lhs: self.lhs.replace_base(f(self.lhs.base())),
            rhs: self.rhs.replace_base(f(self.rhs.base())),
            is_cast: self.is_cast,
        }
    }
}

impl<B: Display, F: Display + Copy> Display for Equality<B, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
    }
}

/// The Eq instance is special, because it is order independent with respect
/// to the left and right hand side.
impl<B: std::cmp::PartialEq, F: std::cmp::PartialEq + Copy> std::cmp::PartialEq for Equality<B, F> {
    fn eq(&self, other: &Self) -> bool {
        // Using an unpack here so compiler warns in case a new field is ever added
        let Equality {
            lhs,
            rhs,
            is_cast: _,
        } = other;
        (lhs == &self.lhs && rhs == &self.rhs) || (rhs == &self.lhs && lhs == &self.rhs)
    }
}

impl<B: Eq, F: Eq + Copy> Eq for Equality<B, F> {}

/// The Hash instance is special, because it is order independent with respect
/// to the left and right hand side.
impl<B: Hash, F: Hash + Copy> Hash for Equality<B, F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        use std::hash::Hasher;
        let mut l = std::collections::hash_map::DefaultHasher::new();
        let mut r = std::collections::hash_map::DefaultHasher::new();

        self.lhs.hash(&mut l);
        self.rhs.hash(&mut r);

        state.write_u64(l.finish().wrapping_add(r.finish()))
    }
}
