use crate::{
    mir::{self, Field}, either::Either, HashSet, HashMap
};

use std::hash::Hash;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Term<B, F>{ kind: Box<TermS<B, F>> }

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TermS<B, F> {
    Base(B),
    RefOf(Term<B, F>),
    DerefOf(Term<B, F>),
    MemberOf{ 
        field: F, 
        inner: Term<B, F>,
    },
    ContainsAt{
        inner: Term<B, F>,
        field: F
    },
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Equality<B, F> {
    lhs: Term<B, F>,
    rhs: Term<B, F>,
}

impl <B, F> Equality<B, F> {
    pub fn rearrange_one_left_to_right(&mut self) {
        use TermS::*;
        match self.lhs.kind() {
            Base(_) => unreachable!(),
            RefOf(r) => {
                self.lhs = *r;
                self.rhs = Term::new_deref_of(self.rhs);
            }
            DerefOf(r) => {
                self.lhs = *r;
                self.rhs = Term::new_ref_of(self.rhs);
            }
            MemberOf { field, inner } => {
                self.lhs = *inner;
                self.rhs = Term::new_contains_at(*field, self.rhs);
            }
            ContainsAt { inner, field } => {
                self.lhs = *inner;
                self.rhs = Term::new_member_of(*field, self.rhs);
            }
            _ => unreachable!()
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

    pub fn bases(&self) -> [&B;2] {
        [self.lhs.base(), self.rhs.base()]
    }
}

impl <B, F> Equality<B, F> {
}

pub fn solve<B: Clone + Hash + Eq, F: Eq + Hash + Clone, V: Clone + Eq + Hash, B0, I: Fn(&B) -> Either<B0, V>>(
    equations: &mut [Equality<B, F>], target: &V, inspect: I
) -> Vec<Term<B0, F>> {
    let mut eqs_with_bases = equations.iter_mut().map(|e| (e.bases().into_iter().filter_map(|b| inspect(b).right()).collect::<Vec<_>>(), e)).collect::<Vec<_>>();
    let mut intermediates : HashMap<V, HashSet<Term<B, F>>> = HashMap::new();
    let mut find_matching = |target:&V| {
        eqs_with_bases.drain_filter(|(bases, eq)| bases.contains(&target)).map(|(_, eq)| eq).collect::<Vec<_>>()
    };

    let mut targets = vec![target.clone()];

    while let Some(target) = targets.pop() {
        if intermediates.contains_key(&target) {
            continue;
        }
        let all_matching = find_matching(&target);
        assert!(all_matching.len() != 0, "No matching equation");
        for matching in all_matching {
            if inspect(matching.lhs.base()).right() != Some(target) {
                matching.swap()
            }
            matching.rearrange_left_to_right();
            if let Either::Right(v) = inspect(matching.rhs.base()) {
                targets.push(v);
            }
            intermediates.entry(target).or_insert_with(HashSet::default).insert(matching.rhs.clone());
        }
    }
    let solutions = vec![];
    let mut targets = intermediates[target].iter().cloned().collect::<Vec<_>>();
    while let Some(target) = targets.pop() {
        match inspect(target.base()) {
            Either::Left(base) => solutions.push(replace_base_and_change_type(base, &target)),
            Either::Right(var) => {
                targets.extend(
                    intermediates[&var].iter().cloned().map(|term| {
                        let to_sub = target.clone();
                        to_sub.sub(term);
                        to_sub
                    })
                )
            }
        }
    }
    solutions
}

impl <B, F> Term<B, F> {
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
        Self{ kind: Box::new(kind) }
    }

    pub fn new_base(base: B) -> Self {
        Term::new(TermS::Base(base))
    }

    pub fn new_deref_of(inner: Self) -> Self {
        Term::new(TermS::DerefOf(inner))
    }

    pub fn new_ref_of(inner: Self) -> Self {
        Term::new(TermS::RefOf(inner))
    }

    pub fn new_member_of(field: F, inner: Self) -> Self {
        Term::new(TermS::MemberOf { field, inner })
    }

    pub fn new_contains_at(field: F, inner: Self) -> Self {
        Term::new(TermS::ContainsAt { field, inner })
    }

    pub fn map<B0, F0, MB: FnMut(&B) -> B0, MF: FnMut(&F) -> F0>(&self, f: MB, g: MF) -> Term<B0, F0> {
        use TermS::*;
        Term::new(
            match self.kind() {
                Base(b) => Base(f(b)),
                RefOf(r) => RefOf(r.map(f, g)),
                DerefOf(r) => DerefOf(r.map(f, g)),
                MemberOf {field, inner} => {
                    let new_field = g(field);
                    MemberOf { field: new_field, inner: inner.map(f, g) }
                }
                ContainsAt { field, inner } => {
                    let new_field = g(field);
                    ContainsAt { field: new_field, inner: inner.map(f, g) }
                }
            }
        )
    }

    pub fn base(&self) -> &B {
        struct BaseCollector<'a, B>(Option<&'a B>);
        impl <'t, B, F> TermVisitor<'t, B, F> for BaseCollector<'t, B> {
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
        impl <'t, B, F> TermMutVisitor<'t, B, F> for BaseReplacer<B, F> {
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

    fn simplify_once(&mut self) -> bool {
        use TermS::*;
        match self.kind_mut() {
            RefOf(Term{ kind: box DerefOf(inner) }) 
            | DerefOf(Term{ kind: box RefOf(inner) }) => {
                *self = inner;
                true
            }
            MemberOf { field, inner: Term { kind: box ContainsAt { field: inner_field, inner}} }
            | ContainsAt { field, inner: Term { kind: box MemberOf{ field: inner_field, inner}} } => {
                assert_eq!(field, inner_field);
                *term = inner;
                true
            }
            _ => false,
        }
    }

    pub fn simplify(&mut self) 
    where F: Eq
    {
        struct Simplifier;
        impl <'t, B, F> TermMutVisitor<'t, B, F> for Simplifier {
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

pub trait TermFolder<B, F, B0, F0> 
{
    /// Note that this visitor function does not rewrap automatically,
    /// instead it expects the specialized visitor methods (e.g.
    /// [`Self::visit_deref_of`]) to create a new term or wrap the inner term
    /// again in [`TermS::DerefOf`].
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
        Term::new(TermS::RefOf(self.visit_term(inner)))
    }

    fn visit_deref_of(&mut self, inner: &Term<B, F>) -> Term<B0, F0> {
        Term::new(TermS::DerefOf(self.visit_term(inner)))
    }


    fn visit_member_of(&mut self, field: &F, inner: &Term<B, F>) -> Term<B0, F0> {
        let new_field = self.visit_field(field);
        Term::new(TermS::MemberOf { field: new_field, inner: self.visit_term(inner) })
    }

    fn visit_contains_at(&mut self, field: &F, inner: &Term<B, F>) -> Term<B0, F0> {
        let new_field = self.visit_field(field);
        Term::new(TermS::ContainsAt { field: new_field, inner: self.visit_term(inner) })
    }

}


pub fn replace_base_and_change_type<B, B0, F: Clone>(base: B, term: &Term<B0, F>) -> Term<B, F> {
    struct TypeChangingBaseReplacer<B>(Option<B>);

    impl <B, F: Clone, B0> TermFolder<B, F, B0, F> for TypeChangingBaseReplacer<B0> {
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

pub trait TermVisitor<'t, B, F> 
{
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

    fn visit_field(&mut self, field: &'t F) {  }

    fn visit_member_of(&mut self, field: &'t F, inner: &'t Term<B, F>)  {
        self.visit_field(field);
        self.visit_term(inner)
    }

    fn visit_contains_at(&mut self, field: &'t F, inner: &'t Term<B, F>) {
        self.visit_field(field);
        self.visit_term(inner)
    }

}
pub trait TermMutVisitor<'t, B, F> 
{
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

    fn visit_field(&mut self, field: &'t mut F) {  }
    fn visit_member_of(&mut self, field: &'t mut F, inner: &'t mut Term<B, F>)  {
        self.super_member_of(field, inner)
    }

    fn super_member_of(&mut self, field: &'t mut F, inner: &'t mut Term<B, F>)  {
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