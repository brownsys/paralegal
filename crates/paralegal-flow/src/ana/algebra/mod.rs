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
    ir::{regal::TargetPlace, GlobalLocal, TypedLocal},
    mir::{self, Field, Place},
    ty,
    utils::{outfile_pls, write_sep, DisplayViaDebug, Print},
    HashMap, HashSet, TyCtxt,
};

use std::{
    fmt::{Display, Write},
    hash::Hash,
};

mod terms;
pub use terms::*;

impl Display for TargetPlace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TargetPlace::Argument(i) => write!(f, "a{}", i.as_usize()),
            TargetPlace::Return => f.write_char('r'),
        }
    }
}

impl<'tcx> Equality<GlobalLocal<'tcx>, DisplayViaDebug<mir::Field>> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        lhs: Term<GlobalLocal<'tcx>, DisplayViaDebug<mir::Field>>,
        rhs: Term<GlobalLocal<'tcx>, DisplayViaDebug<mir::Field>>,
    ) -> Result<Self, String> {
        let slf = Self::unchecked_new(lhs, rhs, false);

        if let Err(e) = equation_sanity_check(tcx, &slf) {
            Err(format!("Sanity check failed for {slf} because: {e}"))
        } else {
            Ok(slf)
        }
    }
}

impl<'tcx> MirEquation<'tcx> {
    pub fn new_mir(
        tcx: TyCtxt<'tcx>,
        lhs: MirTerm<'tcx>,
        rhs: MirTerm<'tcx>,
        is_cast: bool,
    ) -> Self {
        let slf = Self::unchecked_new(lhs, rhs, is_cast);
        let mut slf_copy = slf.clone();
        slf_copy.rearrange_left_to_right();
        assert!(slf_copy.lhs().terms_inside_out().is_empty());
        #[cfg(debug_assertions)]
        if let Err(e) = wrapping_sanity_check(
            tcx,
            slf_copy.lhs().base().ty(),
            slf_copy.rhs().base().ty(),
            slf_copy.rhs().terms_inside_out().to_vec(),
            is_cast,
        ) {
            panic!("Sanity check for equation {slf} failed because: {e}");
        }
        slf
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

    pub struct Graph<D, B, F: Copy> {
        graph: graphmap::GraphMap<B, Operators<F>, Directed>,
        descriptor: D,
    }

    impl<D, B: Copy + Eq + Ord + Hash + Display, F: Copy + Display + Eq + Hash> Graph<D, B, F> {
        pub fn new<GetEq: std::borrow::Borrow<Equality<B, F>>, I: IntoIterator<Item = GetEq>>(
            equations: I,
            descriptor: D,
        ) -> Graph<D, B, F> {
            let mut graph: graphmap::GraphMap<B, Operators<F>, Directed> = Default::default();
            for eq in equations {
                let mut eq: Equality<_, _> = eq.borrow().clone();
                eq.rearrange_left_to_right();
                let from = *eq.rhs().base();
                let to = *eq.lhs().base();
                debug!(
                    "Adding {} -> {} {} ({})",
                    to,
                    from,
                    Print(|fmt| {
                        fmt.write_char('[')?;
                        write_sep(fmt, ", ", eq.rhs().terms_inside_out(), Display::fmt)?;
                        fmt.write_char(']')
                    }),
                    Print(|fmt| {
                        fmt.write_char('[')?;
                        write_sep(fmt, ", ", eq.lhs().terms_inside_out(), Display::fmt)?;
                        fmt.write_char(']')
                    }),
                );
                if let Some(w) = graph.edge_weight_mut(from, to) {
                    w.0.push(eq.rhs().terms_inside_out().to_vec())
                } else {
                    graph.add_edge(
                        from,
                        to,
                        Operators(SmallVec::from_iter([eq.rhs().terms_inside_out().to_vec()])),
                    );
                }
            }
            Graph { graph, descriptor }
        }

        #[allow(clippy::blocks_in_if_conditions)]
        pub fn reachable<T: Fn(B) -> bool>(
            &self,
            from: T,
            is_target: T,
        ) -> Option<(BitSet<usize>, Vec<Operator<F>>)>
        where
            D: Display,
        {
            let Self { graph, descriptor } = self;
            use visit::NodeIndexable;
            let mut short_circuiting: HashMap<_, HashSet<_>> = HashMap::new();
            let mut queue = VecDeque::new();
            for n in self.graph.nodes().filter(|b| from(*b)) {
                queue.push_back((n, BitSet::new_empty(graph.node_bound()), Term::new_base(0)));
                short_circuiting.insert(n, HashSet::from_iter([Term::new_base(0)]));
            }
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
                                write_sep(fmt, ", ", projections.terms_inside_out(), Display::fmt)?;
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
                                        write_sep(
                                            fmt,
                                            ", ",
                                            projections.terms_inside_out(),
                                            Display::fmt,
                                        )?;
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
                                                &|_, (n, _)| "shape=box,color=".to_string()
                                                    + if n == to {
                                                        "red"
                                                    } else if is_target(n) {
                                                        "green"
                                                    } else if from(n) {
                                                        "yellow"
                                                    } else if n == node {
                                                        "purple"
                                                    } else if seen.contains(graph.to_index(n)) {
                                                        "blue"
                                                    } else {
                                                        "black"
                                                    }
                                            )
                                        )
                                        .unwrap();
                                        panic!("Encountered invalid operator combination {one} {two} in {projections}: as op chain {}, while processing {descriptor}. \n  The state of the search on the operator graph at the time the error as found has been dumped to {path}.\n    Yellow is where the search started,\n    blue nodes were seen during the search,\n    the target is green,\n    the red node is the one we were trying to reach and\n    the purple node is where we tried to reach it from.", Print(|fmt| {
                                    fmt.write_char('[')?;
                                    write_sep(fmt, ", ", projections.terms_inside_out(), Display::fmt)?;
                                    fmt.write_char(']')
                                }
                                ));
                                    }
                                }
                            }
                        {
                            if is_target(to) {
                                return Some((seen, projections.into_terms_inside_out()));
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

        pub fn dump<W: std::io::Write, IsTarget: Fn(B) -> bool, DiedHere: Fn(B) -> bool>(
            &self,
            mut w: W,
            is_target: IsTarget,
            died_here: DiedHere,
        ) where
            B: Display,
            F: Display,
        {
            let graph = &self.graph;
            write!(
                w,
                "{}",
                petgraph::dot::Dot::with_attr_getters(
                    graph,
                    &[],
                    &|_, _| "".to_string(),
                    &|_, n| {
                        if is_target(n.0) {
                            "shape=box,color=green"
                        } else if died_here(n.0) {
                            "shape=box,color=red"
                        } else {
                            "shape=box"
                        }
                        .to_string()
                    }
                )
            )
            .unwrap()
        }
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

#[allow(dead_code)]
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
        for mut matching in all_matching.into_iter().cloned() {
            if matching.lhs().base() != &intermediate_target {
                matching.swap()
            }
            saw_target |= is_target(matching.rhs().base());
            matching.rearrange_left_to_right();
            if !is_target(matching.rhs().base()) {
                targets.push(matching.rhs().base().clone());
            }
            intermediates
                .entry(intermediate_target.clone())
                .or_insert_with(HashSet::default)
                .insert(matching.rhs().clone());
        }
    }
    if !saw_target {
        return;
    }
    let matching_intermediate = intermediates.get(from);
    if matching_intermediate.is_none() {
        // debug!("No intermediate found for {from}");
    }
    let mut targets = matching_intermediate
        .into_iter()
        .flat_map(|v| v.iter().cloned())
        .collect::<Vec<_>>();
    let mut seen = HashSet::new();
    while let Some(intermediate_target) = targets.pop() {
        let var = intermediate_target.base();
        if is_target(var) {
            if !register_final(intermediate_target.terms_inside_out().to_vec()) {
                return;
            }
        } else if !seen.contains(var) {
            seen.insert(var.clone());
            if let Some(next_eq) = intermediates.get(var) {
                targets.extend(next_eq.iter().cloned().filter_map(|term| {
                    let mut to_sub = intermediate_target.clone();
                    to_sub.sub(term);
                    let simplifies = to_sub.simplify();
                    (simplifies == Simplified::Yes).then_some(to_sub)
                }))
            } else {
                // debug!("No follow up equation found for {var} on the way from {from}");
            }
        }
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

pub type MirEquation<'tcx> = Equality<TypedLocal<'tcx>, DisplayViaDebug<Field>>;

struct Extractor<'tcx> {
    tcx: TyCtxt<'tcx>,
    equations: HashSet<MirEquation<'tcx>>,
    local_decls: &'tcx mir::LocalDecls<'tcx>,
}

impl<'tcx> Extractor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, local_decls: &'tcx mir::LocalDecls<'tcx>) -> Self {
        Self {
            tcx,
            equations: Default::default(),
            local_decls,
        }
    }
}

pub type MirTerm<'tcx> = Term<TypedLocal<'tcx>, DisplayViaDebug<Field>>;

impl<'tcx> MirTerm<'tcx> {
    pub fn from_place(
        p: Place<'tcx>,
        local_decls: &(impl mir::HasLocalDecls<'tcx> + ?Sized),
    ) -> Self {
        let mut term = Term::new_base(TypedLocal::new(p.local, local_decls));
        for (_, proj) in p.iter_projections() {
            term = term.wrap_in_elem(proj);
        }
        // debug!("{p:?} -> {term}");
        term
    }
}

impl<'tcx> mir::visit::Visitor<'tcx> for Extractor<'tcx> {
    fn visit_assign(
        &mut self,
        place: &mir::Place<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
        _location: mir::Location,
    ) {
        let lhs = MirTerm::from_place(*place, self.local_decls);
        let local_decls = self.local_decls;
        use mir::{AggregateKind, Rvalue::*};
        let mut is_cast = false;
        let rhs_s = match rvalue {
            Use(op) | UnaryOp(_, op)
            => Box::new(op.place().into_iter().map(|p| MirTerm::from_place(p, local_decls)))
                as Box<dyn Iterator<Item = MirTerm>>,
            Cast(_, op, _)
            | ShallowInitBox(op, _) // XXX Not sure this is correct
            => {
                is_cast = true;
                Box::new(op.place().into_iter().map(|p| MirTerm::from_place(p, local_decls)))
                as Box<dyn Iterator<Item = MirTerm>>
            },
            CopyForDeref(place) => Box::new(std::iter::once(MirTerm::from_place(*place, local_decls))) as Box<_>,
            Repeat(..) // safe because it can only ever be populated by constants
            | ThreadLocalRef(..) // This accesses a global variable and thus cannot be tracked
            | NullaryOp(_, _) // Computes a type level constant from thin air
            => Box::new(std::iter::empty()) as Box<_>,
            AddressOf(_, p) // XXX Not sure this is correct but I just want to be safe. The result is a pointer so I don't know how we deal with that
            | Discriminant(p) | Len(p) // This is a weaker (implicit flows) sort of relationship but it is a relationship non the less so I'm adding them here
            => Box::new(std::iter::once(MirTerm::from_place(*p, self.local_decls).add_unknown())),
            Ref(_, _, p) => {
                let term = MirTerm::from_place(*p, local_decls).add_ref_of();
                Box::new(std::iter::once(term)) as Box<_>
            }
            BinaryOp(_, box (op1, op2)) | CheckedBinaryOp(_, box (op1, op2)) => Box::new(
                // I'm annoyed about having to add an unknown here but since
                // this changes types it's the only way to go.
                [op1, op2]
                    .into_iter()
                    .flat_map(|op| op.place().into_iter())
                    .map(|op| MirTerm::from_place(op, local_decls).add_unknown())
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
                                MirTerm::from_place(place, local_decls)
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
                            MirTerm::from_place(place, local_decls)
                                .add_contains_at(DisplayViaDebug(i.into()))
                        )
                    });
                    Box::new(it) as Box<_>
                }
                AggregateKind::Tuple => Box::new(ops.iter().enumerate().filter_map(|(i, op)| {
                    op.place()
                        .map(|p| MirTerm::from_place(p, local_decls).add_contains_at(DisplayViaDebug(i.into())))
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
                            MirTerm::from_place(op.place()?, local_decls)
                                .add_contains_at(DisplayViaDebug(Field::from_usize(i))),
                        )
                    });
                    Box::new(it) as Box<_>
                }
                AggregateKind::Array(_) => {
                    let it = ops.iter().filter_map(|op| {
                        Some(
                            MirTerm::from_place(op.place()?, local_decls).add_array_with()
                        )
                    });
                    Box::new(it) as Box<_>
                }
            },
        };
        // For some reason two async closures don't compare equal at the moment
        // here so I construct this unchecked.
        self.equations
            .extend(rhs_s.map(|rhs| Equality::unchecked_new(lhs.clone(), rhs, is_cast)))
    }
}

/// Extract a fact base from the statements in an MIR body.
pub fn extract_equations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'tcx mir::Body<'tcx>,
) -> HashSet<MirEquation<'tcx>> {
    use mir::visit::Visitor;
    let mut extractor = Extractor::new(tcx, &body.local_decls);
    extractor.visit_body(body);
    extractor.equations
}

pub fn equation_sanity_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    eq: &Equality<GlobalLocal<'tcx>, DisplayViaDebug<Field>>,
) -> Result<(), String> {
    #[cfg(debug_assertions)]
    {
        let mut eq = eq.clone();
        eq.rearrange_left_to_right();
        assert!(eq.lhs().terms_inside_out().is_empty());

        let is_cast = eq.is_cast();
        let (lhs, rhs) = eq.decompose();
        let wrap = rhs.terms_inside_out().iter().copied();

        return wrapping_sanity_check(tcx, lhs.base.ty, rhs.base.ty, wrap, is_cast);
    }

    #[cfg(not(debug_assertions))]
    return Ok(());
}

#[cfg(debug_assertions)]
pub fn wrapping_sanity_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    left: ty::Ty<'tcx>,
    right: ty::Ty<'tcx>,
    wrap: impl IntoIterator<Item = Operator<DisplayViaDebug<mir::Field>>>,
    is_cast: bool,
) -> Result<(), String> {
    use crate::utils::APoorPersonsEquivalenceCheck;
    use mir::tcx::PlaceTy;
    use mir::ProjectionElem::{self, *};
    use Operator::*;

    let mut left = PlaceTy {
        ty: left,
        variant_index: None,
    };
    let mut right = PlaceTy {
        ty: right,
        variant_index: None,
    };

    let wrap = wrap.into_iter().collect::<Vec<_>>();
    if wrap.iter().copied().any(Operator::is_unknown) {
        return Ok(());
    }
    let apply_deref = |target: &mut PlaceTy<'tcx>| *target = target.projection_ty(tcx, Deref);
    let apply_field = |target: &mut PlaceTy<'tcx>, idx: mir::Field| {
        *target = match target.ty.kind() {
            ty::TyKind::Closure(_did, sub) => {
                assert!(target.variant_index.is_none(), "{target:?}");
                PlaceTy {
                    ty: sub
                        .as_closure()
                        .upvar_tys()
                        .nth(idx.as_usize())
                        .unwrap_or_else(|| {
                            panic!("{target:?} does not have enough upvars for {idx:?}")
                        }),
                    variant_index: None,
                }
            }
            ty::TyKind::Generator(did, substs, _) => {
                // I'm guessing here as to how generators actually work. My
                // working theory is that there are a number of "prefix" fields
                // that are accessible without using a variant index, followed
                // by a number of "state types" which are only accessible after
                // downcasting to a specific variant. My assumption also is that
                // both those indices are 0-based.
                //
                // Unfortunately I can't think if a good way to be defensive
                // wrt. those assumptions.
                let generator = substs.as_generator();
                debug!(
                    "Prefix tys: {:?}, State tys: {:?}",
                    Vec::from_iter(generator.prefix_tys()),
                    generator
                        .state_tys(*did, tcx)
                        .map(Vec::from_iter)
                        .collect::<Vec<_>>()
                );
                let ty = if let Some(v) = target.variant_index {
                    generator
                        .state_tys(*did, tcx)
                        .nth(v.as_usize())
                        .expect("Not enough variants")
                        .nth(idx.as_usize())
                        .expect("Not enough types")
                } else {
                    generator.prefix_tys().nth(idx.as_usize()).unwrap()
                };
                PlaceTy {
                    ty,
                    variant_index: None,
                }
            }
            _ => PlaceTy {
                ty: target.field_ty(tcx, idx),
                variant_index: None,
            },
        }
    };
    let apply_index =
        |target: &mut PlaceTy<'tcx>| *target = target.projection_ty(tcx, Index(0_usize.into()));
    let apply_downcast = |target: &mut PlaceTy<'tcx>, v| {
        *target = target.projection_ty(tcx, mir::PlaceElem::Downcast(None, v))
    };

    // This is kind of complicated because the wrappings need to be applied in
    // opposite order to both of the two types. I think there's also an
    // invariant by which you only have "in" wrappings first followed by "out"
    // wrappings (meaning whether they need to apply to left or right).
    //
    // As such it is split into one closure that applies the wraps that need to
    // apply to the right type, then the one's that need to apply to the left
    // one.
    wrap.into_iter()
        .filter_map(|op| match op {
            DerefOf => {
                apply_deref(&mut right);
                None
            }
            RefOf => Some(Deref),
            MemberOf(f) => {
                apply_field(&mut right, f.0);
                None
            }
            ContainsAt(f) => Some(Field(*f, ())),
            IndexOf => {
                apply_index(&mut right);
                None
            }
            ArrayWith => Some(Index(())),
            Operator::Downcast(v) => {
                apply_downcast(&mut right, v.into());
                None
            }
            Operator::Upcast(v) => Some(ProjectionElem::Downcast(None, v.into())),
            Unknown => unreachable!(),
        })
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .for_each(|for_left| match for_left {
            Deref => apply_deref(&mut left),
            Field(f, _) => apply_field(&mut left, f),
            Index(_) => apply_index(&mut left),
            ProjectionElem::Downcast(_, v) => apply_downcast(&mut left, v),
            _ => unreachable!(),
        });
    if is_cast {
        return Ok(());
    }
    let l_ty = tcx.normalize_erasing_regions(ty::ParamEnv::reveal_all(), left.ty);
    let r_ty = tcx.normalize_erasing_regions(ty::ParamEnv::reveal_all(), right.ty);
    if left.variant_index == right.variant_index && l_ty.is_similar_enough(&r_ty, tcx.lang_items())
    {
        Ok(())
    } else {
        Err(format!(
            "Sanity check failed:\n     {left:?}\n  != {right:?}"
        ))
    }
}
