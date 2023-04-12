//! The place algebra
//!
//! This module defines the algebra for reasoning about relations of
//! abstract locations in memory.
//!
//! To run [`solve`], which can tell you how two memory locations relate, you
//! need a fact base made up of a set of [`Equality`] equations. Equations
//! comprise of [`Term`]s which in turn are a base with [`Operator`]s layered
//! around.
//!
//! For instance to extract a fact base from an MIR body use
//! [`extract_equations`].

use petgraph::visit::IntoEdges;

use crate::{
    either::Either,
    ir::regal::TargetPlace,
    mir::{self, Field, Local, Place},
    utils::{outfile_pls, write_sep, DisplayViaDebug, Print},
    HashMap, HashSet, Symbol, TyCtxt,
};

use std::{
    fmt::{Debug, Display, Write},
    hash::{Hash, Hasher},
};

/// Terms in the projection algebra
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Term<B, F: Copy> {
    /// The base of the term
    base: B,
    /// Operators applied to the term (in reverse order)
    terms: Vec<Operator<F>>,
}

fn display_term_pieces<F: Display + Copy, B: Display>(
    f: &mut std::fmt::Formatter<'_>,
    terms: &[Operator<F>],
    base: &B,
) -> std::fmt::Result {
    use Operator::*;
    for t in terms.iter().rev() {
        match t {
            RefOf => f.write_str("&("),
            DerefOf => f.write_str("*("),
            ContainsAt(field) => write!(f, "{{ .{}: ", field),
            Upcast(_, s) => write!(f, "(#{s}"),
            Unknown => write!(f, "(?"),
            ArrayWith => f.write_char('['),
            _ => f.write_char('('),
        }?
    }
    write!(f, "{}", base)?;
    for t in terms.iter() {
        match t {
            MemberOf(field) => write!(f, ".{})", field),
            ContainsAt(_) => f.write_str(" }"),
            Downcast(_, s) => write!(f, " #{s})"),
            ArrayWith => f.write_char(']'),
            IndexOf => write!(f, "[])"),
            _ => f.write_char(')'),
        }?
    }
    Ok(())
}

impl<B: Display, F: Display + Copy> Display for Term<B, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        display_term_pieces(f, &self.terms, &self.base)
    }
}

impl Display for TargetPlace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TargetPlace::Argument(i) => write!(f, "a{}", i.as_usize()),
            TargetPlace::Return => f.write_char('r'),
        }
    }
}

type VariantIdx = usize;

/// An operator in the projection algebra.
#[derive(Clone, Eq, Hash, Debug, Copy, PartialEq)]
pub enum Operator<F: Copy> {
    RefOf,
    DerefOf,
    MemberOf(F),
    ContainsAt(F),
    IndexOf,
    ArrayWith,
    Downcast(Option<Symbol>, VariantIdx),
    Upcast(Option<Symbol>, VariantIdx),
    Unknown,
}

impl<F: Copy + std::fmt::Display> std::fmt::Display for Operator<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Operator::*;
        match self {
            RefOf => f.write_char('&'),
            DerefOf => f.write_char('*'),
            Unknown => f.write_char('?'),
            MemberOf(m) => write!(f, ".{m}"),
            ContainsAt(m) => write!(f, "@{m}"),
            Downcast(_, s) => write!(f, "#{s:?}"),
            Upcast(_, s) => write!(f, "^{s:?}"),
            IndexOf => f.write_str("$"),
            ArrayWith => f.write_str("[]"),
        }
    }
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
        }
    }
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
            Downcast(s, v) => Upcast(s, v),
            Upcast(s, v) => Downcast(s, v),
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
            (MemberOf(f), ContainsAt(g)) | (ContainsAt(g), MemberOf(f)) if f != g => {
                Cancel::NonOverlappingField(f, g)
            }
            (Downcast(_, v1), Upcast(_, v2)) | (Upcast(_, v2), Downcast(_, v1)) if v1 != v2 => {
                Cancel::NonOverlappingVariant(v1, v2)
            }
            _ if self == other.flip() => Cancel::CancelOne,
            _ => Cancel::Remains,
        }
    }

    /// Apply a function to the field, creating a new operator
    pub fn map_field<F0: Copy, G: FnMut(F) -> F0>(self, mut g: G) -> Operator<F0> {
        use Operator::*;
        match self {
            RefOf => RefOf,
            DerefOf => DerefOf,
            MemberOf(f) => MemberOf(g(f)),
            ContainsAt(f) => ContainsAt(g(f)),
            Upcast(s, v) => Upcast(s, v),
            Downcast(s, v) => Downcast(s, v),
            Unknown => Unknown,
            IndexOf => IndexOf,
            ArrayWith => ArrayWith,
        }
    }
}

/// An equation in the algebra
#[derive(Clone, Debug)]
pub struct Equality<B, F: Copy> {
    lhs: Term<B, F>,
    rhs: Term<B, F>,
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
        let Equality { lhs, rhs } = other;
        (lhs == &self.lhs && rhs == &self.rhs) || (rhs == &self.lhs && lhs == &self.rhs)
    }
}

impl<B: Eq, F: Eq + Copy> Eq for Equality<B, F> {}

/// The Hash instance is special, because it is order independent with respect
/// to the left and right hand side.
impl<B: Hash, F: Hash + Copy> Hash for Equality<B, F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let mut l = std::collections::hash_map::DefaultHasher::new();
        let mut r = std::collections::hash_map::DefaultHasher::new();

        self.lhs.hash(&mut l);
        self.rhs.hash(&mut r);

        state.write_u64(l.finish().wrapping_add(r.finish()))
    }
}

impl<B, F: Copy> Equality<B, F> {
    /// Create a new equation
    pub fn new(lhs: Term<B, F>, rhs: Term<B, F>) -> Self {
        Self { lhs, rhs }
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
        }
    }
}

fn partial_cmp_terms<'a, F: Copy + Eq>(
    mut left: &'a [Operator<F>],
    mut right: &'a [Operator<F>],
) -> Option<std::cmp::Ordering> {
    use std::cmp::Ordering::*;
    let greater = left.len() > right.len();
    if !greater {
        std::mem::swap(&mut left, &mut right);
    }
    let mut matches = false;
    for i in 0..(left.len() - right.len()) {
        if left[i..].iter().zip(right.iter()).all(|(l, r)| l == r) {
            matches = true;
            break;
        }
    }
    if !matches {
        None
    } else {
        Some(if left.len() == right.len() {
            Equal
        } else if greater {
            Greater
        } else {
            Less
        })
    }
}

/// Solve for the relationship of two bases.
///
/// Returns all terms `t` such that `from = t(to)`. If no terms are returned the
/// two bases are not related (memory non interference).
///
/// If you need to instead solve for the relationship of two terms `t1`, `t2`, generate two
/// new bases `x`, `y` then extend the fact base with the equations `x = t1`,
/// `y = t2` and solve for `x` and `y` instead.
///
pub fn solve<
    B: Clone + Hash + Eq + Display,
    F: Eq + Hash + Clone + Copy + Display,
    GetEq: std::borrow::Borrow<Equality<B, F>>,
>(
    equations: &[GetEq],
    from: &B,
    to: &B,
) -> Vec<Vec<Operator<F>>> {
    let mut solutions = vec![];
    solve_with(
        equations,
        from,
        |found| found == to,
        |solution| {
            solutions.push(solution);
            true
        },
    );
    solutions
}

pub fn solve_reachable<
    B: Clone + Hash + Eq + Display,
    F: Eq + Hash + Clone + Copy + Display,
    GetEq: std::borrow::Borrow<Equality<B, F>>,
    IsTarget: FnMut(&B) -> bool,
>(
    equations: &[GetEq],
    from: &B,
    to: IsTarget,
) -> bool {
    let mut reachable = false;
    solve_with(equations, from, to, |_| {
        reachable = true;
        false
    });
    reachable
}

fn solve_with<
    B: Clone + Hash + Eq + Display,
    F: Eq + Hash + Clone + Copy + Display,
    GetEq: std::borrow::Borrow<Equality<B, F>>,
    RegisterFinal: FnMut(Vec<Operator<F>>) -> bool,
    IsTarget: FnMut(&B) -> bool,
>(
    equations: &[GetEq],
    from: &B,
    mut is_target: IsTarget,
    mut register_final: RegisterFinal,
) {
    if is_target(from) {
        register_final(vec![]);
        return;
    }
    let mut eqs_with_bases = equations
        .iter()
        .map(|e| {
            (
                e.borrow().bases().into_iter().collect::<Vec<_>>(),
                e.borrow(),
            )
        })
        .collect::<Vec<_>>();
    let mut intermediates: HashMap<B, HashSet<Term<B, F>>> = HashMap::new();
    let mut find_matching = |target: &B| {
        eqs_with_bases
            .drain_filter(|(bases, _eq)| bases.contains(&target))
            .map(|(_, eq)| eq)
            .collect::<Vec<_>>()
    };

    let mut targets = vec![from.clone()];

    let mut saw_target = false;

    while let Some(intermediate_target) = targets.pop() {
        if intermediates.contains_key(&intermediate_target) {
            continue;
        }
        let all_matching = find_matching(&intermediate_target);
        // if all_matching.is_empty() {
        //     debug!(
        //         "No matching equation for intermediate target {} from {}",
        //         intermediate_target, from
        //     );
        // }
        for mut matching in all_matching.into_iter().cloned() {
            if matching.lhs.base() != &intermediate_target {
                matching.swap()
            }
            saw_target |= is_target(matching.rhs.base());
            matching.rearrange_left_to_right();
            if !is_target(matching.rhs.base()) {
                targets.push(matching.rhs.base().clone());
            }
            intermediates
                .entry(intermediate_target.clone())
                .or_insert_with(HashSet::default)
                .insert(matching.rhs);
        }
    }
    debug!(
        "Found the intermediates\n{}",
        Print(|fmt: &mut std::fmt::Formatter<'_>| {
            for (k, vs) in intermediates.iter() {
                write!(fmt, "  {k}: ")?;
                write_sep(fmt, " || ", vs, Display::fmt)?;
                fmt.write_str("\n")?;
            }
            Ok(())
        })
    );
    if !saw_target {
        debug!("Never saw final target, abandoning solving early");
        return;
    }
    let matching_intermediate = intermediates.get(from);
    if matching_intermediate.is_none() {
        debug!("No intermediate found for {from}");
    }
    let mut targets = matching_intermediate
        .into_iter()
        .flat_map(|v| v.iter().cloned())
        .collect::<Vec<_>>();
    let mut seen = HashSet::new();
    while let Some(intermediate_target) = targets.pop() {
        let var = intermediate_target.base();
        if is_target(var) {
            if !register_final(intermediate_target.terms) {
                return;
            }
        } else if !seen.contains(var) {
            seen.insert(var.clone());
            if let Some(next_eq) = intermediates.get(&var) {
                targets.extend(next_eq.iter().cloned().filter_map(|term| {
                    let mut to_sub = intermediate_target.clone();
                    to_sub.sub(term);
                    to_sub.simplify().then_some(to_sub)
                }))
            } else {
                debug!("No follow up equation found for {var} on the way from {from}");
            }
        }
    }
}

fn vec_drop_range<T>(v: &mut Vec<T>, r: std::ops::Range<usize>) {
    let ptr = v.as_mut_ptr();
    for i in r.clone() {
        unsafe { drop(ptr.add(i)) }
    }
    unsafe {
        std::ptr::copy(ptr.add(r.end), ptr.add(r.start), v.len() - r.end);
        v.set_len(v.len() - r.len());
    }
}

impl<B, F: Copy> Term<B, F> {
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

    pub fn add_downcast(mut self, symbol: Option<Symbol>, idx: VariantIdx) -> Self {
        self.terms.push(Operator::Downcast(symbol, idx));
        self
    }

    pub fn add_upcast(mut self, symbol: Option<Symbol>, idx: VariantIdx) -> Self {
        self.terms.push(Operator::Upcast(symbol, idx));
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

    pub fn base(&self) -> &B {
        &self.base
    }

    pub fn sub(&mut self, other: Self) {
        let Self { base, mut terms } = other;
        self.base = base;
        terms.append(&mut self.terms);
        std::mem::swap(&mut self.terms, &mut terms)
    }

    pub fn simplify(&mut self) -> bool
    where
        F: Eq + Display,
        B: Display,
    {
        let l = self.terms.len();
        let old_terms = std::mem::replace(&mut self.terms, Vec::with_capacity(l));
        let mut it = old_terms.into_iter().peekable();
        let mut valid = true;
        let mut after_first_unknown = None;
        let mut after_last_unknown = None;
        while let Some(i) = it.next() {
            if let Some(next) = it.peek().cloned() {
                let cancel = i.cancel(next);
                match cancel {
                    Cancel::NonOverlappingField(f, g) => {
                        valid = false;
                    }
                    Cancel::NonOverlappingVariant(v1, v2) => {
                        valid = false;
                    }
                    Cancel::CancelBoth => {
                        it.next();
                        continue;
                    }
                    Cancel::CancelOne => {
                        continue;
                    }
                    _ => (),
                }
            }
            self.terms.push(i);
            if i.is_unknown() {
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
        valid
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
}

impl<B> Term<B, Field> {
    pub fn wrap_in_elem(self, elem: mir::PlaceElem) -> Self {
        use mir::ProjectionElem::*;
        match elem {
            Field(f, _) => self.add_member_of(f),
            Deref => self.add_deref_of(),
            Downcast(s, v) => self.add_downcast(s, v.as_usize()),
            _ => unimplemented!("{:?}", elem),
        }
    }
}

pub type MirEquation = Equality<DisplayViaDebug<Local>, DisplayViaDebug<Field>>;

struct Extractor<'tcx> {
    tcx: TyCtxt<'tcx>,
    equations: HashSet<MirEquation>,
}

impl<'tcx> Extractor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            equations: Default::default(),
        }
    }
}

type MirTerm = Term<DisplayViaDebug<Local>, DisplayViaDebug<Field>>;

impl From<Place<'_>> for MirTerm {
    fn from(p: Place<'_>) -> Self {
        let mut term = Term::new_base(DisplayViaDebug(p.local));
        for (_, proj) in p.iter_projections() {
            term = term.wrap_in_elem(proj);
        }
        term.replace_fields(DisplayViaDebug)
    }
}

impl From<&'_ Place<'_>> for MirTerm {
    fn from(p: &'_ Place<'_>) -> Self {
        MirTerm::from(*p)
    }
}

impl<'tcx> mir::visit::Visitor<'tcx> for Extractor<'tcx> {
    fn visit_assign(
        &mut self,
        place: &mir::Place<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
        _location: mir::Location,
    ) {
        let lhs = MirTerm::from(place);
        use mir::{AggregateKind, Rvalue::*};
        let rhs_s = match rvalue {
            Use(op) | UnaryOp(_, op) | Cast(_, op, _) 
            | ShallowInitBox(op, _) // XXX Not sure this is correct
            => Box::new(op.place().into_iter().map(|p| p.into()))
                as Box<dyn Iterator<Item = MirTerm>>,
            Repeat(..) // safe because it can only ever be populated by constants
            | ThreadLocalRef(..) // This accesses a global variable and thus cannot be tracked
            | NullaryOp(_, _) // Computes a type level constant from thin air
            => Box::new(std::iter::empty()) as Box<_>,
            AddressOf(_, p) // XXX Not sure this is correct but I just want to be safe. The result is a pointer so I don't know how we deal with that
            | Discriminant(p) | Len(p) // This is a weaker (implicit flows) sort of relationship but it is a relationship non the less so I'm adding them here
            => Box::new(std::iter::once(MirTerm::from(p).add_unknown())), 
            Ref(_, _, p) => {
                let term = MirTerm::from(p).add_ref_of();
                Box::new(std::iter::once(term)) as Box<_>
            }
            BinaryOp(_, box (op1, op2)) | CheckedBinaryOp(_, box (op1, op2)) => Box::new(
                [op1, op2]
                    .into_iter()
                    .flat_map(|op| op.place().into_iter())
                    .map(|op| op.into()),
            )
                as Box<_>,
            Aggregate(box kind, ops) => match kind {
                AggregateKind::Adt(def_id, idx, _, _, _) => {
                    let adt_def = self.tcx.adt_def(*def_id);
                    let variant = adt_def.variant(*idx);
                    let iter = variant
                        .fields
                        .iter()
                        .enumerate()
                        .zip(ops.iter())
                        .filter_map(|((i, _field), op)| {
                            let place = op.place()?;
                            // let field = mir::ProjectionElem::Field(
                            //     Field::from_usize(i),
                            //     field.ty(self.tcx, substs),
                            // );
                            Some(
                                MirTerm::from(place)
                                    .add_contains_at(DisplayViaDebug(Field::from_usize(i))),
                            )
                        });
                    Box::new(iter) as Box<_>
                }
                AggregateKind::Closure(def_id, _) => {
                    // XXX This is a speculative way of handling this. Instead
                    // we should look up actual field info but I wasn't able to
                    // find a function that retrieves a closure's layout
                    let it = ops.iter().enumerate().filter_map(|(i, op)| {
                        let place = op.place()?;
                        Some(
                            MirTerm::from(place)
                                .add_contains_at(DisplayViaDebug(i.into()))
                        )
                    });
                    Box::new(it) as Box<_>
                }
                AggregateKind::Tuple => Box::new(ops.iter().enumerate().filter_map(|(i, op)| {
                    op.place()
                        .map(|p| MirTerm::from(p).add_contains_at(DisplayViaDebug(i.into())))
                })) as Box<_>,
                AggregateKind::Generator(_gen_id, _, _) => {
                    // I think this is the proper way to do this but the fields
                    // were sometimes empty and I don't know why so I'm doing
                    // the hacky thing below instead
                    // let gen_def =
                    // self.tcx.generator_layout(*gen_id).unwrap();
                    // debug!("variant fields {:?}", gen_def);
                    // let variant = gen_def.variant_fields.raw.first().unwrap();
                    // assert_eq!(variant.len(), ops.len());
                    // let it = variant.iter_enumerated().zip(ops).filter_map(|((field, _), op)| {
                    //     Some(MirTerm::from(op.place()?).add_contains_at(DisplayViaDebug(field)))
                    // });
                    let it = ops.iter().enumerate().filter_map(|(i, op)| {
                        Some(
                            MirTerm::from(op.place()?)
                                .add_contains_at(DisplayViaDebug(Field::from_usize(i))),
                        )
                    });
                    Box::new(it) as Box<_>
                }
                AggregateKind::Array(_) => {
                    let it = ops.iter().filter_map(|op| {
                        Some(
                            MirTerm::from(op.place()?).add_index_of()
                        )
                    });
                    Box::new(it) as Box<_>
                }
            },
        };
        self.equations.extend(rhs_s.map(|rhs| Equality {
            lhs: lhs.clone(),
            rhs,
        }))
    }
}

/// Extract a fact base from the statements in an MIR body.
pub fn extract_equations<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> HashSet<MirEquation> {
    use mir::visit::Visitor;
    let mut extractor = Extractor::new(tcx);
    extractor.visit_body(body);
    extractor.equations
}
