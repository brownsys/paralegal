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

use crate::{
    ir::regal::TargetPlace,
    mir::{self, Field, Local, Place},
    ty,
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
    pub base: B,
    /// Operators applied to the term (in reverse order)
    pub terms: Vec<Operator<F>>,
}

pub fn display_term_pieces<F: Display + Copy, B: Display>(
    f: &mut std::fmt::Formatter<'_>,
    terms: &[Operator<F>],
    base: &B,
) -> std::fmt::Result {
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
    Downcast(VariantIdx),
    Upcast(VariantIdx),
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
            Downcast(s) => write!(f, "#{s:?}"),
            Upcast(s) => write!(f, "^{s:?}"),
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

/// An equation in the algebra
#[derive(Clone, Debug)]
pub struct Equality<B, F: Copy> {
    pub lhs: Term<B, F>,
    pub rhs: Term<B, F>,
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

#[allow(dead_code)]
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

pub mod graph {
    use std::collections::VecDeque;

    use super::*;
    use crate::rust::rustc_index::bit_set::BitSet;
    use petgraph::{visit::EdgeRef, *};
    extern crate smallvec;
    use smallvec::SmallVec;

    pub type Graph<B, F> = graphmap::GraphMap<B, Operators<F>, Directed>;

    pub fn new<
        B: Copy + Eq + Ord + Hash + Display,
        F: Copy + Display,
        GetEq: std::borrow::Borrow<Equality<B, F>>,
        I: IntoIterator<Item = GetEq>,
    >(
        equations: I,
    ) -> Graph<B, F> {
        let mut graph = Graph::new();
        for eq in equations {
            let mut eq: Equality<_, _> = eq.borrow().clone();
            eq.rearrange_left_to_right();
            debug!(
                "Adding {} -> {} {} ({})",
                eq.rhs.base(),
                eq.lhs.base(),
                Print(|fmt| {
                    fmt.write_char('[')?;
                    write_sep(fmt, ", ", eq.rhs.terms.iter(), Display::fmt)?;
                    fmt.write_char(']')
                }),
                Print(|fmt| {
                    fmt.write_char('[')?;
                    write_sep(fmt, ", ", eq.lhs.terms.iter(), Display::fmt)?;
                    fmt.write_char(']')
                }),
            );
            if let Some(w) = graph.edge_weight_mut(*eq.lhs.base(), *eq.rhs.base()) {
                w.0.push(eq.rhs.terms)
            } else {
                graph.add_edge(
                    *eq.rhs.base(),
                    *eq.lhs.base(),
                    Operators(SmallVec::from_iter([eq.rhs.terms])),
                );
            }
        }
        graph
    }

    #[allow(clippy::blocks_in_if_conditions)]
    pub fn reachable<
        B: Display + Copy + Hash + Eq + Ord,
        F: Hash + Eq + Display + Copy,
        T: Fn(B) -> bool,
    >(
        from: B,
        is_target: T,
        graph: &Graph<B, F>,
    ) -> Option<(BitSet<usize>, Vec<Operator<F>>)> {
        use visit::NodeIndexable;
        let mut short_circuiting: HashMap<_, HashSet<_>> =
            HashMap::from_iter([(from, HashSet::from_iter([Term::new_base(0)]))]);
        let seen = BitSet::new_empty(graph.node_bound());
        let mut queue = VecDeque::from_iter([(from, seen, Term::new_base(0))]);
        while let Some((node, mut seen, projections)) = queue.pop_front() {
            seen.insert(graph.to_index(node));
            for next in graph
                .edges(node)
                .chain(graph.edges_directed(node, Incoming))
            {
                let (to, is_flipped) = if next.source() == node {
                    (next.target(), false)
                } else {
                    (next.source(), true)
                };
                if seen.contains(graph.to_index(to)) {
                    continue;
                }
                for weight in next.weight().0.iter() {
                    debug!(
                        "{node} {} {to} {}, {is_flipped}",
                        Print(|fmt| {
                            fmt.write_char('[')?;
                            write_sep(fmt, ", ", projections.terms.iter(), Display::fmt)?;
                            fmt.write_char(']')
                        }),
                        Print(|fmt| {
                            fmt.write_char('[')?;
                            write_sep(fmt, ", ", weight.iter(), Display::fmt)?;
                            fmt.write_char(']')
                        }),
                    );
                    let mut projections = projections.clone();
                    if next.weight().0.is_empty()
                        || {
                            if is_flipped {
                                projections = projections
                                    .extend(weight.iter().copied().map(Operator::flip).rev());
                            } else {
                                projections = projections.extend(weight.iter().copied());
                            }
                            debug!(
                                "{}",
                                Print(|fmt| {
                                    fmt.write_char('[')?;
                                    write_sep(fmt, ", ", projections.terms.iter(), Display::fmt)?;
                                    fmt.write_char(']')
                                }),
                            );
                            match projections.simplify() {
                                Simplified::Yes => true,
                                Simplified::NonOverlapping => false,
                                Simplified::Invalid(one, two) => {
                                    let path = "algebra-invalidation-err.gv";
                                    let mut outf = outfile_pls(path).unwrap();
                                    use std::io::Write;
                                    write!(
                                        outf,
                                        "{}",
                                        petgraph::dot::Dot::with_attr_getters(
                                            graph,
                                            &[],
                                            &|_, _| "".to_string(),
                                            &|_, (n, _)| if seen.contains(graph.to_index(n)) {
                                                "shape=box,color=blue".to_string()
                                            } else if n == to {
                                                "shape=box,color=red".to_string()
                                            } else if is_target(n) {
                                                "shape=box,color=green".to_string()
                                            } else if n == from {
                                                "shape=box,color=aqua".to_string()
                                            } else {
                                                "shape=box".to_string()
                                            }
                                        )
                                    )
                                    .unwrap();
                                    panic!("Encountered invalid operator combination {one} {two} in {projections}: as op chain {}. The state of the search on the operator graph at the time the error as found has been dumped to {path}.", Print(|fmt| {
                                    fmt.write_char('[')?;
                                    write_sep(fmt, ", ", projections.terms.iter(), Display::fmt)?;
                                    fmt.write_char(']')
                                }
                                ));
                                }
                            }
                        }
                    {
                        if is_target(to) {
                            return Some((seen, projections.terms));
                        }
                        if short_circuiting
                            .entry(to)
                            .or_insert_with(HashSet::new)
                            .insert(projections.clone())
                        {
                            queue.push_back((to, seen.clone(), projections));
                        }
                    }
                }
            }
        }
        None
    }

    pub fn dump<
        B: graphmap::NodeTrait + Display,
        F: Copy + Display,
        W: std::io::Write,
        IsTarget: Fn(B) -> bool,
        DiedHere: Fn(B) -> bool,
    >(
        mut w: W,
        graph: &Graph<B, F>,
        is_target: IsTarget,
        died_here: DiedHere,
    ) {
        write!(
            w,
            "{}",
            petgraph::dot::Dot::with_attr_getters(graph, &[], &|_, _| "".to_string(), &|_, n| {
                if is_target(n.0) {
                    "shape=box,color=green"
                } else if died_here(n.0) {
                    "shape=box,color=red"
                } else {
                    "shape=box"
                }
                .to_string()
            })
        )
        .unwrap()
    }
    pub struct Operators<F: Copy>(SmallVec<[Vec<Operator<F>>; 1]>);

    impl<F: Copy + Display> std::fmt::Display for Operators<F> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write_sep(f, ", ", self.0.iter(), |elem, f| {
                display_term_pieces(f, elem.as_slice(), &0)
            })
        }
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
    B: Clone + Hash + Eq + Display + Ord,
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
    B: Clone + Hash + Eq + Display + Ord,
    F: Eq + Hash + Clone + Copy + Display,
    GetEq: std::borrow::Borrow<Equality<B, F>>,
    IsTarget: Fn(&B) -> bool,
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

use std::sync::atomic;

lazy_static! {
    static ref IOUTCTR: atomic::AtomicI32 = atomic::AtomicI32::new(0);
}

fn dump_intermediates<
    B: Clone + Hash + Display + Eq + Ord,
    F: Eq + Hash + Copy + Display,
    H: Fn(&B) -> bool,
    D: Fn(&B) -> bool,
>(
    intr: &HashMap<B, HashSet<Term<B, F>>>,
    is_target: H,
    died_here: D,
) {
    use petgraph::graphmap::*;
    use petgraph::prelude::*;
    let graph = GraphMap::<_, _, Directed>::from_edges(
        intr.iter()
            .flat_map(|(k, v)| v.iter().map(move |t| (k, &t.base, t.replace_base(0_usize)))),
    );
    use std::io::Write;
    let name = format!(
        "intermediates_{}.gv",
        IOUTCTR.fetch_add(1, atomic::Ordering::Relaxed)
    );
    let mut outf = outfile_pls(&name).unwrap();
    debug!("Dumped intermediates to {name}");
    write!(
        outf,
        "{}",
        petgraph::dot::Dot::with_attr_getters(&graph, &[], &|_, _| "".to_string(), &|_, n| {
            if is_target(n.0) {
                "shape=box,color=green"
            } else if died_here(n.0) {
                "shape=box,color=red"
            } else {
                "shape=box"
            }
            .to_string()
        })
    )
    .unwrap()
}

pub fn solve_with<
    B: Clone + Hash + Eq + Display + Ord,
    F: Eq + Hash + Clone + Copy + Display,
    GetEq: std::borrow::Borrow<Equality<B, F>>,
    RegisterFinal: FnMut(Vec<Operator<F>>) -> bool,
    IsTarget: Fn(&B) -> bool,
>(
    equations: &[GetEq],
    from: &B,
    is_target: IsTarget,
    mut register_final: RegisterFinal,
) {
    let is_debug_target = format!("{from}") == "_32 @ root";
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
    if !saw_target {
        if is_debug_target {
            debug!("Never saw final target, abandoning solving early");
        }
        return;
    }
    let matching_intermediate = intermediates.get(from);
    if matching_intermediate.is_none() {
        // debug!("No intermediate found for {from}");
    }
    let mut died = HashSet::new();
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
            if let Some(next_eq) = intermediates.get(var) {
                targets.extend(next_eq.iter().cloned().filter_map(|term| {
                    let mut to_sub = intermediate_target.clone();
                    to_sub.sub(term);
                    let simplifies = to_sub.simplify();
                    if simplifies != Simplified::Yes && is_debug_target {
                        debug!("{to_sub} does not simplify");
                        died.insert(to_sub.base.clone());
                    }
                    (simplifies == Simplified::Yes).then_some(to_sub)
                }))
            } else {
                // debug!("No follow up equation found for {var} on the way from {from}");
            }
        }
    }

    if is_debug_target {
        dump_intermediates(&intermediates, &is_target, |b| died.contains(b));
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

#[derive(Clone, Eq, Hash, PartialEq)]
pub enum Simplified<F: Copy> {
    Yes,
    NonOverlapping,
    Invalid(Operator<F>, Operator<F>),
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

impl<B> Term<B, DisplayViaDebug<Field>> {
    pub fn wrap_in_elem(self, elem: mir::PlaceElem) -> Self {
        use mir::ProjectionElem::*;
        match elem {
            Field(f, _) => self.add_member_of(DisplayViaDebug(f)),
            Deref => self.add_deref_of(),
            Downcast(s, v) => self.add_downcast(s, v.as_usize()),
            Index(_) | ConstantIndex { .. } => self.add_index_of(),
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

pub type MirTerm = Term<DisplayViaDebug<Local>, DisplayViaDebug<Field>>;

impl From<Place<'_>> for MirTerm {
    fn from(p: Place<'_>) -> Self {
        let mut term = Term::new_base(DisplayViaDebug(p.local));
        for (_, proj) in p.iter_projections() {
            term = term.wrap_in_elem(proj);
        }
        debug!("{p:?} -> {term}");
        term
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
            CopyForDeref(place) => Box::new(std::iter::once(place.into())) as Box<_>,
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
                    let is_enum = adt_def.flags().contains(ty::AdtFlags::IS_ENUM);
                    let iter = variant
                        .fields
                        .iter()
                        .enumerate()
                        .zip(ops.iter())
                        .filter_map(move |((i, _field), op)| {
                            let place = op.place()?;
                            // let field = mir::ProjectionElem::Field(
                            //     Field::from_usize(i),
                            //     field.ty(self.tcx, substs),
                            // );
                            let mut term =
                                MirTerm::from(place)
                                    .add_contains_at(DisplayViaDebug(Field::from_usize(i)));
                            if is_enum {
                                term = term.add_upcast(None, idx.as_usize());
                            }
                            Some(term)
                        });
                    Box::new(iter) as Box<_>
                }
                AggregateKind::Closure(_def_id, _) => {
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
                            MirTerm::from(op.place()?).add_array_with()
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
