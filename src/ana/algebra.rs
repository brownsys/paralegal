use crate::{
    either::Either,
    mir::{self, Field, Place, Local},
    HashMap, HashSet, TyCtxt,
};

use std::{
    fmt::Debug,
    hash::{Hash, Hasher},
    borrow::Cow,
    cell::RefCell
};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Term<B, F: Copy> {
    base: B,
    terms: Vec<TermS<F>>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy)]
pub enum TermS<F : Copy> {
    RefOf,
    DerefOf,
    MemberOf(F),
    ContainsAt(F),
}

impl <F:Copy> TermS<F> {
    pub fn flip(self) -> Self {
        use TermS::*;
        match self {
            RefOf => DerefOf,
            DerefOf => RefOf,
            MemberOf(f) => ContainsAt(f),
            ContainsAt(f) => MemberOf(f),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Equality<B, F: Copy> {
    lhs: Term<B, F>,
    rhs: Term<B, F>,
}

impl<B: std::cmp::PartialEq, F: std::cmp::PartialEq + Copy> std::cmp::PartialEq for Equality<B, F> {
    fn eq(&self, other: &Self) -> bool {
        // Using an unpack here so compiler warns in case a new field is ever added
        let Equality { lhs, rhs } = other;
        (lhs == &self.lhs && rhs == &self.rhs) || (rhs == &self.lhs && lhs == &self.rhs)
    }
}

impl<B: Eq, F: Eq + Copy> Eq for Equality<B, F> {}

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
    pub fn rearrange_left_to_right(&mut self) {
        self.rhs.terms.extend(self.lhs.terms.drain(..).rev().map(TermS::flip));
    }

    pub fn swap(&mut self) {
        std::mem::swap(&mut self.lhs, &mut self.rhs)
    }

    pub fn bases(&self) -> [&B; 2] {
        [self.lhs.base(), self.rhs.base()]
    }
}

impl<B, F: Copy> Equality<B, F> {}

pub fn solve<
    B: Clone + Hash + Eq,
    F: Eq + Hash + Clone + Copy,
    V: Clone + Eq + Hash,
    B0,
    I: Fn(&B) -> Either<B0, V>,
    GetEq: std::borrow::Borrow<Equality<B, F>>
>(
    equations: &[GetEq],
    target: &V,
    inspect: I,
) -> Vec<Term<B0, F>> {
    let mut eqs_with_bases = equations
        .iter()
        .map(|e| {
            (
                e.borrow()
                    .bases()
                    .into_iter()
                    .filter_map(|b| inspect(b).right())
                    .collect::<Vec<_>>(),
                e.borrow(),
            )
        })
        .collect::<Vec<_>>();
    let mut intermediates: HashMap<V, HashSet<Term<B, F>>> = HashMap::new();
    let mut find_matching = |target: &V| {
        eqs_with_bases
            .drain_filter(|(bases, eq)| bases.contains(&target))
            .map(|(_, eq)| eq)
            .collect::<Vec<_>>()
    };

    let mut targets = vec![target.clone()];

    while let Some(target) = targets.pop() {
        if intermediates.contains_key(&target) {
            continue;
        }
        let all_matching = find_matching(&target);
        assert!(all_matching.len() != 0, "No matching equation");
        for mut matching in all_matching.into_iter().cloned() {
            if inspect(matching.lhs.base()).right() != Some(target.clone()) {
                matching.swap()
            }
            matching.rearrange_left_to_right();
            if let Either::Right(v) = inspect(matching.rhs.base()) {
                targets.push(v);
            }
            intermediates
                .entry(target.clone())
                .or_insert_with(HashSet::default)
                .insert(matching.rhs);
        }
    }
    let mut solutions = vec![];
    let mut targets = intermediates[target].iter().cloned().collect::<Vec<_>>();
    while let Some(target) = targets.pop() {
        match inspect(target.base()) {
            Either::Left(base) => solutions.push(target.replace_base(base)),
            Either::Right(var) => targets.extend(intermediates[&var].iter().cloned().map(|term| {
                let mut to_sub = target.clone();
                to_sub.sub(term);
                to_sub
            })),
        }
    }
    solutions
}

impl<B, F: Copy> Term<B, F> {
    pub fn kind(&self) -> TermS<F> {
        self.terms[0]
    }

    pub fn is_base(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn new_base(base: B) -> Self {
        Term { base, terms: vec![] }
    }

    pub fn add_deref_of(mut self) -> Self {
        self.terms.push(TermS::DerefOf);
        self
    }

    pub fn add_ref_of(mut self) -> Self {
        self.terms.push(TermS::RefOf);
        self
    }

    pub fn add_member_of(mut self, field: F) -> Self {
        self.terms.push(TermS::MemberOf(field));
        self
    }

    pub fn add_contains_at(mut self, field: F) -> Self {
        self.terms.push(TermS::ContainsAt(field));
        self
    }

    pub fn base(&self) -> &B {
        &self.base
    }

    pub fn sub(&mut self, other: Self) {
        let Self { base, terms } = other;
        self.base = base;
        self.terms.extend(terms)
    }

    pub fn simplify(&mut self)
    where
        F: Eq + Debug,
    {
        let l = self.terms.len();
        let old_terms = std::mem::replace(&mut self.terms, Vec::with_capacity(l));
        let mut it = old_terms.into_iter().peekable();
        while let Some(i) = it.next() {
            if Some(i.flip()) == it.peek().cloned() {
                it.next();
            } else {
                self.terms.push(i);
            }
        }
    }
    pub fn replace_base<B0>(&self, base: B0) -> Term<B0, F> {
        Term {
            base, terms: self.terms.clone()
        }
    }
}


impl <B> Term<B, Field> {
    pub fn wrap_in_elem(self, elem: mir::PlaceElem) -> Self {
        use mir::ProjectionElem::*;
        match elem {
            Field(f, _) => self.add_contains_at(f),
            Deref => self.add_deref_of(),
            _ => unimplemented!()
        }
    }
}


type MirEquation = Equality<mir::Local, Field>;

struct Extractor<'tcx> {
    tcx: TyCtxt<'tcx>,
    equations: HashSet<MirEquation>,
}

type MirTerm = Term<Local, Field>;

impl From<Place<'_>> for MirTerm {
    fn from(p: Place<'_>) -> Self {
        let mut term = MirTerm::new_base(p.local);
        for (_, proj) in p.iter_projections() {
            term = term.wrap_in_elem(proj);
        }
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
        location: mir::Location,
    ) {
        let lhs = MirTerm::from(place);
        use mir::{AggregateKind, Rvalue::*};
        let rhs_s = match rvalue {
            Use(op) | UnaryOp(_, op) => Box::new(op.place().into_iter().map(|p| p.into()))
                as Box<dyn Iterator<Item = MirTerm>>,
            Ref(_, _, p) => Box::new(std::iter::once(MirTerm::from(p).add_ref_of())) as Box<_>,
            BinaryOp(_, box (op1, op2)) | CheckedBinaryOp(_, box (op1, op2)) => Box::new(
                [op1, op2]
                    .into_iter()
                    .flat_map(|op| op.place().into_iter())
                    .map(|op| op.into()),
            )
                as Box<_>,
            Aggregate(box kind, ops) => match kind {
                AggregateKind::Adt(def_id, idx, substs, _, _) => {
                    let adt_def = self.tcx.adt_def(*def_id);
                    let variant = adt_def.variant(*idx);
                    let iter = variant
                        .fields
                        .iter()
                        .enumerate()
                        .zip(ops.iter())
                        .filter_map(|((i, field), op)| {
                            let place = op.place()?;
                            // let field = mir::ProjectionElem::Field(
                            //     Field::from_usize(i),
                            //     field.ty(self.tcx, substs),
                            // );
                            Some(
                                MirTerm::from(place)
                                .add_contains_at(Field::from_usize(i)))
                        });
                    Box::new(iter) as Box<_>
                }
                AggregateKind::Tuple => Box::new(ops.iter().enumerate().filter_map(|(i, op)| {
                    op.place()
                        .map(|p| MirTerm::from(p).add_contains_at(i.into()))
                })) as Box<_>,
                _ => {
                    debug!("Unhandled rvalue {rvalue:?}");
                    Box::new(std::iter::empty()) as Box<_>
                }
            },

            other => {
                debug!("Unhandled rvalue {other:?}");
                Box::new(std::iter::empty()) as Box<_>
            }
        };
        self.equations.extend(rhs_s.map(|rhs| Equality {
            lhs: lhs.clone(),
            rhs,
        }))
    }
}

struct VariableGenerator<T>(T);

impl <T> VariableGenerator<T> {
    pub fn new(t: T) -> Self {
        Self(t)
    }

    pub fn generate(&mut self) -> T 
    where 
        T: std::ops::Add<usize, Output=T> + Copy
    {
        let t = self.0.clone();
        self.0 = self.0 + 1;
        t
    }
}

impl <T: From<usize>> Default for VariableGenerator<T> {
    fn default() -> Self {
        Self::new(0.into())
    }
}

pub struct PlaceResolver{
    equations: Vec<MirEquation>,
    variable_generator: RefCell<VariableGenerator<Local>>,
}

impl PlaceResolver {
    pub fn resolve(&self, from: Place, to: Place) -> Term<(), Field> {
        let target_term = MirTerm::from(to);
        let target = self.variable_generator.borrow_mut().generate();
        let source_term = MirTerm::from(from);
        let source = self.variable_generator.borrow_mut().generate();
        let equations = 
            self.equations.iter().map(Cow::Borrowed)
                .chain([
                    Cow::Owned(Equality { rhs: Term::new_base(target), lhs: target_term}),
                    Cow::Owned(Equality { rhs: Term::new_base(source), lhs: source_term})
                ]).collect::<Vec<_>>();
        let mut results = solve(&equations, &target, |&local| if local == target { Either::Left(())} else { Either::Right(local)});
        assert_eq!(results.len(), 1);
        results.pop().unwrap()
    }
}