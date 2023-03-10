use crate::{
    either::Either,
    mir::{self, Field},
    HashMap, HashSet, TyCtxt,
};

use std::{
    fmt::Debug,
    hash::{Hash, Hasher},
};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Term<B, F> {
    kind: Box<TermS<B, F>>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TermS<B, F> {
    Base(B),
    RefOf(Term<B, F>),
    DerefOf(Term<B, F>),
    MemberOf { field: F, inner: Term<B, F> },
    ContainsAt { inner: Term<B, F>, field: F },
}

#[derive(Clone, Debug)]
pub struct Equality<B, F> {
    lhs: Term<B, F>,
    rhs: Term<B, F>,
}

impl<B: std::cmp::PartialEq, F: std::cmp::PartialEq> std::cmp::PartialEq for Equality<B, F> {
    fn eq(&self, other: &Self) -> bool {
        // Using an unpack here so compiler warns in case a new field is ever added
        let Equality { lhs, rhs } = other;
        (lhs == &self.lhs && rhs == &self.rhs) || (rhs == &self.lhs && lhs == &self.rhs)
    }
}

impl<B: Eq, F: Eq> Eq for Equality<B, F> {}

impl<B: Hash, F: Hash> Hash for Equality<B, F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let mut l = std::collections::hash_map::DefaultHasher::new();
        let mut r = std::collections::hash_map::DefaultHasher::new();

        self.lhs.hash(&mut l);
        self.rhs.hash(&mut r);

        state.write_u64(l.finish().wrapping_add(r.finish()))
    }
}

impl<B, F> Equality<B, F> {
    pub fn rearrange_one_left_to_right(&mut self) {
        use TermS::*;
        match self.lhs.kind() {
            Base(_) => unreachable!(),
            RefOf(r) => {
                self.lhs = *r;
                self.rhs = self.rhs.add_deref_of();
            }
            DerefOf(r) => {
                self.lhs = *r;
                self.rhs = self.rhs.add_ref_of();
            }
            MemberOf { field, inner } => {
                self.lhs = *inner;
                self.rhs = self.rhs.add_contains_at(*field);
            }
            ContainsAt { inner, field } => {
                self.lhs = *inner;
                self.rhs = self.rhs.add_member_of(*field);
            }
            _ => unreachable!(),
        }
    }

    pub fn rearrange_left_to_right(&mut self) {
        while !self.lhs.is_base() {
            self.rearrange_one_left_to_right()
        }
    }

    pub fn swap(&mut self) {
        std::mem::swap(&mut self.lhs, &mut self.rhs)
    }

    pub fn bases(&self) -> [&B; 2] {
        [self.lhs.base(), self.rhs.base()]
    }
}

impl<B, F> Equality<B, F> {}

pub fn solve<
    B: Clone + Hash + Eq,
    F: Eq + Hash + Clone,
    V: Clone + Eq + Hash,
    B0,
    I: Fn(&B) -> Either<B0, V>,
>(
    equations: &[Equality<B, F>],
    target: &V,
    inspect: I,
) -> Vec<Term<B0, F>> {
    let mut eqs_with_bases = equations
        .iter()
        .map(|e| {
            (
                e.bases()
                    .into_iter()
                    .filter_map(|b| inspect(b).right())
                    .collect::<Vec<_>>(),
                e,
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
        for matching in all_matching.into_iter().cloned() {
            if inspect(matching.lhs.base()).right() != Some(target) {
                matching.swap()
            }
            matching.rearrange_left_to_right();
            if let Either::Right(v) = inspect(matching.rhs.base()) {
                targets.push(v);
            }
            intermediates
                .entry(target)
                .or_insert_with(HashSet::default)
                .insert(matching.rhs);
        }
    }
    let solutions = vec![];
    let mut targets = intermediates[target].iter().cloned().collect::<Vec<_>>();
    while let Some(target) = targets.pop() {
        match inspect(target.base()) {
            Either::Left(base) => solutions.push(replace_base_and_change_type(base, &target)),
            Either::Right(var) => targets.extend(intermediates[&var].iter().cloned().map(|term| {
                let to_sub = target.clone();
                to_sub.sub(term);
                to_sub
            })),
        }
    }
    solutions
}

impl<B, F> Term<B, F> {
    pub fn kind(&self) -> &TermS<B, F> {
        &self.kind
    }

    pub fn kind_mut(&mut self) -> &mut TermS<B, F> {
        &mut self.kind
    }

    pub fn is_base(&self) -> bool {
        matches!(self.kind(), TermS::Base(..))
    }

    pub fn new(kind: TermS<B, F>) -> Self {
        Self {
            kind: Box::new(kind),
        }
    }

    pub fn new_base(base: B) -> Self {
        Term::new(TermS::Base(base))
    }

    pub fn add_deref_of(self) -> Self {
        Term::new(TermS::DerefOf(self))
    }

    pub fn add_ref_of(self) -> Self {
        Term::new(TermS::RefOf(self))
    }

    pub fn add_member_of(self, field: F) -> Self {
        Term::new(TermS::MemberOf { field, inner: self })
    }

    pub fn add_contains_at(self, field: F) -> Self {
        Term::new(TermS::ContainsAt { field, inner: self })
    }

    pub fn map<B0, F0, MB: FnMut(&B) -> B0, MF: FnMut(&F) -> F0>(
        &self,
        f: MB,
        g: MF,
    ) -> Term<B0, F0> {
        use TermS::*;
        Term::new(match self.kind() {
            Base(b) => Base(f(b)),
            RefOf(r) => RefOf(r.map(f, g)),
            DerefOf(r) => DerefOf(r.map(f, g)),
            MemberOf { field, inner } => {
                let new_field = g(field);
                MemberOf {
                    field: new_field,
                    inner: inner.map(f, g),
                }
            }
            ContainsAt { field, inner } => {
                let new_field = g(field);
                ContainsAt {
                    field: new_field,
                    inner: inner.map(f, g),
                }
            }
        })
    }

    pub fn base(&self) -> &B {
        struct BaseCollector<'a, B>(Option<&'a B>);
        impl<'t, B, F> TermVisitor<'t, B, F> for BaseCollector<'t, B> {
            fn visit_base(&mut self, base: &'t B) {
                self.0 = Some(base)
            }
        }
        let mut c = BaseCollector(None);
        c.visit_term(self);
        c.0.unwrap()
    }

    pub fn sub(&mut self, other: Self) {
        struct BaseReplacer<B, F>(Option<Term<B, F>>);
        impl<'t, B, F> TermMutVisitor<'t, B, F> for BaseReplacer<B, F> {
            fn visit_term(&mut self, term: &'t mut Term<B, F>) {
                if term.is_base() {
                    *term = self.0.expect("Double substitute");
                } else {
                    self.super_term(term)
                }
            }
        }

        let mut repl = BaseReplacer(Some(other));
        repl.visit_term(self);
        assert!(repl.0.is_none());
    }

    fn simplify_once(&mut self) -> bool
    where
        F: Eq + Debug,
    {
        use TermS::*;
        match self.kind_mut() {
            RefOf(Term {
                kind: box DerefOf(inner),
            })
            | DerefOf(Term {
                kind: box RefOf(inner),
            }) => {
                *self = *inner;
                true
            }
            MemberOf {
                field,
                inner:
                    Term {
                        kind:
                            box ContainsAt {
                                field: inner_field,
                                inner,
                            },
                    },
            }
            | ContainsAt {
                field,
                inner:
                    Term {
                        kind:
                            box MemberOf {
                                field: inner_field,
                                inner,
                            },
                    },
            } => {
                assert_eq!(field, inner_field);
                *self = *inner;
                true
            }
            _ => false,
        }
    }

    pub fn simplify(&mut self)
    where
        F: Eq + Debug,
    {
        struct Simplifier;
        impl<'t, B, F: Eq + Debug> TermMutVisitor<'t, B, F> for Simplifier {
            fn visit_term(&mut self, term: &'t mut Term<B, F>) {
                // Additional loop here so we simplify this outer part all the
                // way without causing an endless loop (which is the case if you
                // instead tried calling `self.visit_term` again at the end).
                while term.simplify_once() {}
                self.super_term(term)
            }
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

pub trait TermFolder<B, F, B0, F0> {
    /// Note that this visitor function does not rewrap automatically,
    /// instead it expects the specialized visitor methods (e.g.
    /// [`Self::visit_deref_of`]) to create a new term or wrap the inner term
    /// again (e.g. in [`TermS::DerefOf`]).
    fn visit_term(&mut self, term: &Term<B, F>) -> Term<B0, F0> {
        use TermS::*;
        match term.kind() {
            Base(b) => self.visit_base(b),
            RefOf(r) => self.visit_ref_of(r),
            DerefOf(r) => self.visit_deref_of(r),
            MemberOf { field, inner } => self.visit_member_of(field, inner),
            ContainsAt { field, inner } => self.visit_contains_at(field, inner),
        }
    }

    fn visit_base(&mut self, base: &B) -> Term<B0, F0>;
    fn visit_field(&mut self, field: &F) -> F0;

    fn visit_ref_of(&mut self, inner: &Term<B, F>) -> Term<B0, F0> {
        self.visit_term(inner).add_ref_of()
    }

    fn visit_deref_of(&mut self, inner: &Term<B, F>) -> Term<B0, F0> {
        self.visit_term(inner).add_deref_of()
    }

    fn visit_member_of(&mut self, field: &F, inner: &Term<B, F>) -> Term<B0, F0> {
        let new_field = self.visit_field(field);
        self.visit_term(inner).add_member_of(new_field)
    }

    fn visit_contains_at(&mut self, field: &F, inner: &Term<B, F>) -> Term<B0, F0> {
        let new_field = self.visit_field(field);
        self.visit_term(inner).add_contains_at(new_field)
    }
}

pub fn replace_base_and_change_type<B, B0, F: Clone>(base: B, term: &Term<B0, F>) -> Term<B, F> {
    struct TypeChangingBaseReplacer<B>(Option<B>);

    impl<B, F: Clone, B0> TermFolder<B, F, B0, F> for TypeChangingBaseReplacer<B0> {
        fn visit_base(&mut self, base: &B) -> Term<B0, F> {
            Term::new_base(self.0.expect("Double substitute"))
        }

        fn visit_field(&mut self, field: &F) -> F {
            field.clone()
        }
    }
    let mut replacer = TypeChangingBaseReplacer(Some(base));
    let result = replacer.visit_term(term);
    assert!(replacer.0.is_none());
    result
}

pub trait TermVisitor<'t, B, F> {
    fn visit_term(&mut self, term: &'t Term<B, F>) {
        use TermS::*;
        match term.kind() {
            Base(b) => self.visit_base(b),
            RefOf(r) => self.visit_ref_of(r),
            DerefOf(r) => self.visit_deref_of(r),
            MemberOf { field, inner } => self.visit_member_of(field, inner),
            ContainsAt { field, inner } => self.visit_contains_at(field, inner),
        }
    }

    fn visit_base(&mut self, base: &'t B) {}

    fn visit_ref_of(&mut self, inner: &'t Term<B, F>) {
        self.visit_term(inner)
    }

    fn visit_deref_of(&mut self, inner: &'t Term<B, F>) {
        self.visit_term(inner)
    }

    fn visit_field(&mut self, field: &'t F) {}

    fn visit_member_of(&mut self, field: &'t F, inner: &'t Term<B, F>) {
        self.visit_field(field);
        self.visit_term(inner)
    }

    fn visit_contains_at(&mut self, field: &'t F, inner: &'t Term<B, F>) {
        self.visit_field(field);
        self.visit_term(inner)
    }
}
pub trait TermMutVisitor<'t, B, F> {
    fn visit_term(&mut self, term: &'t mut Term<B, F>) {
        self.super_term(term)
    }

    fn super_term(&mut self, term: &'t mut Term<B, F>) {
        use TermS::*;
        match term.kind_mut() {
            Base(b) => self.visit_base(b),
            RefOf(r) => self.visit_ref_of(r),
            DerefOf(r) => self.visit_deref_of(r),
            MemberOf { field, inner } => self.visit_member_of(field, inner),
            ContainsAt { field, inner } => self.visit_contains_at(field, inner),
        }
    }

    fn visit_base(&mut self, base: &'t mut B) {}

    fn visit_ref_of(&mut self, inner: &'t mut Term<B, F>) {
        self.super_ref_of(inner)
    }

    fn super_ref_of(&mut self, inner: &'t mut Term<B, F>) {
        self.visit_term(inner)
    }

    fn visit_deref_of(&mut self, inner: &'t mut Term<B, F>) {
        self.super_deref_of(inner)
    }

    fn super_deref_of(&mut self, inner: &'t mut Term<B, F>) {
        self.visit_term(inner)
    }

    fn visit_field(&mut self, field: &'t mut F) {}
    fn visit_member_of(&mut self, field: &'t mut F, inner: &'t mut Term<B, F>) {
        self.super_member_of(field, inner)
    }

    fn super_member_of(&mut self, field: &'t mut F, inner: &'t mut Term<B, F>) {
        self.visit_field(field);
        self.visit_term(inner)
    }
    fn visit_contains_at(&mut self, field: &'t mut F, inner: &'t mut Term<B, F>) {
        self.super_contains_at(field, inner)
    }

    fn super_contains_at(&mut self, field: &'t mut F, inner: &'t mut Term<B, F>) {
        self.visit_field(field);
        self.visit_term(inner)
    }
}

struct Extractor<'tcx> {
    tcx: TyCtxt<'tcx>,
    equations: HashSet<Equality<mir::Local, Field>>,
}

impl<'tcx> mir::visit::Visitor<'tcx> for Extractor<'tcx> {
    fn visit_assign(
        &mut self,
        place: &mir::Place<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
        location: mir::Location,
    ) {
        type MirTerm = Term<mir::Local, Field>;
        let lhs = place.into();
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
                            let field = mir::ProjectionElem::Field(
                                Field::from_usize(i),
                                field.ty(self.tcx, substs),
                            );
                            place.into().add_contains_at(field)
                        });
                    Box::new(iter) as Box<_>
                }
                AggregateKind::Tuple => Box::new(ops.iter().enumerate().map(|(i, op)| {
                    op.place()
                        .into_iter()
                        .map(|p| p.into().add_contains_at(i.into()))
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
