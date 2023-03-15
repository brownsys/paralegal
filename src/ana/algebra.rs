use crate::{
    either::Either,
    mir::{self, Field, Local, Place},
    HashMap, HashSet, TyCtxt, ir::regal::TargetPlace,
};

use std::{
    borrow::Cow,
    cell::RefCell,
    fmt::{Debug, Display, Write},
    hash::{Hash, Hasher},
};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Term<B, F: Copy> {
    base: B,
    terms: Vec<TermS<F>>,
}

impl <B: Display, F: Display + Copy> Display for Term<B, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TermS::*;
        for t in self.terms.iter().rev() {
            match t {
                RefOf => f.write_str("&("),
                DerefOf => f.write_str("*("),
                MemberOf(_) => f.write_char('('),
                ContainsAt(field) =>
                    write!(f, "{{ .{} = ", field),
            }?
        }
        write!(f, "{}", self.base)?;
        for t in self.terms.iter().rev() {
            match t {
                MemberOf(field) => write!(f, ".{})", field),
                ContainsAt(_) => f.write_str(" }"),
                _ => f.write_char(')'),
            }?
        }
        Ok(())
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

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy)]
pub enum TermS<F: Copy> {
    RefOf,
    DerefOf,
    MemberOf(F),
    ContainsAt(F),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy)]
pub enum Cancel<F: Copy> {
    NonOverlapping(F, F),
    Cancels,
    Remains,
}

impl<F: Copy> TermS<F> {
    pub fn flip(self) -> Self {
        use TermS::*;
        match self {
            RefOf => DerefOf,
            DerefOf => RefOf,
            MemberOf(f) => ContainsAt(f),
            ContainsAt(f) => MemberOf(f),
        }
    }

    pub fn cancel(self, other: Self) -> Cancel<F> 
    where F: PartialEq 
    {
        use TermS::*;
        match (self, other) {
            (MemberOf(f), ContainsAt(g)) | (ContainsAt(g), MemberOf(f)) if f != g => Cancel::NonOverlapping(f, g),
            _ if self == other.flip() => Cancel::Cancels,
            _ => Cancel::Remains,
        }
    }

    pub fn map_field<F0: Copy, G: FnMut(F) -> F0>(self, mut g: G) -> TermS<F0> {
        use TermS::*;
        match self {
            RefOf => RefOf,
            DerefOf => DerefOf,
            MemberOf(f) => MemberOf(g(f)),
            ContainsAt(f) => ContainsAt(g(f)),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Equality<B, F: Copy> {
    lhs: Term<B, F>,
    rhs: Term<B, F>,
}

impl <B: Display, F:Display + Copy> Display for Equality<B, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
    }
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
        self.rhs
            .terms
            .extend(self.lhs.terms.drain(..).rev().map(TermS::flip));
    }

    pub fn swap(&mut self) {
        std::mem::swap(&mut self.lhs, &mut self.rhs)
    }

    pub fn bases(&self) -> [&B; 2] {
        [self.lhs.base(), self.rhs.base()]
    }
}

impl<B, F: Copy> Equality<B, F> {}

pub struct Print<F>(F);

impl <F: Fn(&mut std::fmt::Formatter<'_>) -> std::fmt::Result> Display for Print<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (self.0)(f)
    }
}

pub fn solve<
    B: Clone + Hash + Eq + Display,
    F: Eq + Hash + Clone + Copy + Display,
    V: Clone + Eq + Hash + Debug,
    B0,
    I: Fn(&B) -> Either<B0, V>,
    GetEq: std::borrow::Borrow<Equality<B, F>>,
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
            .drain_filter(|(bases, _eq)| bases.contains(&target))
            .map(|(_, eq)| eq)
            .collect::<Vec<_>>()
    };

    let mut targets = vec![target.clone()];

    while let Some(intermediate_target) = targets.pop() {
        if intermediates.contains_key(&intermediate_target) {
            continue;
        }
        let all_matching = find_matching(&intermediate_target);
        if all_matching.is_empty() {
            debug!("No matching equation for intermediate target {:?} from {:?}", intermediate_target, target);
        }
        for mut matching in all_matching.into_iter().cloned() {
            if inspect(matching.lhs.base()).right() != Some(intermediate_target.clone()) {
                matching.swap()
            }
            matching.rearrange_left_to_right();
            if let Either::Right(v) = inspect(matching.rhs.base()) {
                targets.push(v);
            }
            intermediates
                .entry(intermediate_target.clone())
                .or_insert_with(HashSet::default)
                .insert(matching.rhs);
        }
    }
    debug!("Found the intermediates");
    for (k, vs) in intermediates.iter() {
        debug!("  {k:?}: {}", Print(|f: &mut std::fmt::Formatter| {
            let mut first = true;
            for term in vs {
                if first {
                    first = false;
                } else {
                    f.write_str(" || ")?;
                }
                write!(f, "{}", term)?;
            }
            Ok(())
        }));
    }
    let mut solutions = vec![];
    let mut targets = intermediates[target].iter().cloned().collect::<Vec<_>>();
    while let Some(intermediate_target) = targets.pop() {
        match inspect(intermediate_target.base()) {
            Either::Left(base) => solutions.push(intermediate_target.replace_base(base)),
            Either::Right(var) =>
                if let Some(next_eq) = intermediates.get(&var) {
                    targets.extend(next_eq.iter().cloned().filter_map(|term| {
                        let mut to_sub = intermediate_target.clone();
                        to_sub.sub(term);
                        to_sub.simplify().then_some(to_sub)
                    }))
                } else {
                    debug!("No follow up equation found for {var:?} on the way from {target:?}");
                }
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
        Term {
            base,
            terms: vec![],
        }
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
        let Self { base, mut terms } = other;
        self.base = base;
        terms.append(&mut self.terms);
        std::mem::swap(&mut self.terms, &mut terms)
    }

    pub fn simplify(&mut self) -> bool
    where
        F: Eq + Display,
        B: Display
    {
        let l = self.terms.len();
        let old_terms = std::mem::replace(&mut self.terms, Vec::with_capacity(l));
        let mut it = old_terms.into_iter().peekable();
        let mut valid = true;
        while let Some(i) = it.next() {
            if let Some(next) = it.peek().cloned() {
                match i.cancel(next) {
                    Cancel::NonOverlapping(f, g) => {
                        debug!("Rejecting {self} because {f} != {g}");
                        valid = false;
                    }
                    Cancel::Cancels => {
                        it.next();
                        continue;
                    }
                    _ => (),
                }
            } 
            self.terms.push(i);
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
    where B: Clone
    {
        Term {
            base: self.base.clone(),
            terms: self.terms.iter().map(|f| f.map_field(&mut g)).collect()
        }
    }
}

impl<B> Term<B, Field> {
    pub fn wrap_in_elem(self, elem: mir::PlaceElem) -> Self {
        use mir::ProjectionElem::*;
        match elem {
            Field(f, _) => self.add_member_of(f),
            Deref => self.add_deref_of(),
            _ => unimplemented!(),
        }
    }
}

type MirEquation = Equality<DisplayViaDebug<Local>, DisplayViaDebug<Field>>;

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
        location: mir::Location,
    ) {
        let lhs = MirTerm::from(place);
        use mir::{AggregateKind, Rvalue::*};
        let rhs_s = match rvalue {
            Use(op) | UnaryOp(_, op) => Box::new(op.place().into_iter().map(|p| p.into()))
                as Box<dyn Iterator<Item = MirTerm>>,
            Ref(_, _, p) => {
                let term = MirTerm::from(p).add_ref_of();
                Box::new(std::iter::once(term)) as Box<_>
            },
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
                            Some(MirTerm::from(place).add_contains_at(DisplayViaDebug(Field::from_usize(i))))
                        });
                    Box::new(iter) as Box<_>
                }
                AggregateKind::Tuple => Box::new(ops.iter().enumerate().filter_map(|(i, op)| {
                    op.place()
                        .map(|p| MirTerm::from(p).add_contains_at(DisplayViaDebug(i.into())))
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

impl<T> VariableGenerator<T> {
    pub fn new(t: T) -> Self {
        Self(t)
    }

    pub fn generate(&mut self) -> T
    where
        T: std::ops::Add<usize, Output = T> + Copy,
    {
        let t = self.0.clone();
        self.0 = self.0 + 1;
        t
    }
}

impl<T: From<usize>> Default for VariableGenerator<T> {
    fn default() -> Self {
        Self::new(0.into())
    }
}

pub struct PlaceResolver {
    equations: Vec<MirEquation>,
    variable_generator: RefCell<VariableGenerator<Local>>,
}

#[derive(Hash, Eq, Ord, PartialEq, PartialOrd, Clone, Copy)]
pub struct DisplayViaDebug<T>(T);

impl <T: Debug> Display for DisplayViaDebug<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as Debug>::fmt(&self.0, f)
    }
}

impl <T: Debug> Debug for DisplayViaDebug<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl <T> std::ops::Deref for DisplayViaDebug<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PlaceResolver {
    pub fn construct<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Self {
        use mir::visit::Visitor;
        let mut extractor = Extractor::new(tcx);
        extractor.visit_body(body);
        let equations = extractor.equations.into_iter().collect();

        let variable_generator = RefCell::new(VariableGenerator::new(mir::Local::from_usize(
            body.local_decls.len(),
        )));
        debug!("Equations {:?}", equations);
        debug!("Generating variables from {:?}", variable_generator.borrow().0);

        Self {
            equations,
            variable_generator,
        }
    }

    pub fn try_resolve(&self, from: Place, to: Place) -> Option<Term<(), DisplayViaDebug<Field>>> {
        let target_term = MirTerm::from(to);
        let target = DisplayViaDebug(self.variable_generator.borrow_mut().generate());
        let source_term = MirTerm::from(from);
        let source = DisplayViaDebug(self.variable_generator.borrow_mut().generate());
        let equations = self
            .equations
            .iter()
            .map(Cow::Borrowed)
            .chain([
                Cow::Owned(Equality {
                    rhs: Term::new_base(target),
                    lhs: target_term,
                }),
                Cow::Owned(Equality {
                    rhs: Term::new_base(source),
                    lhs: source_term,
                }),
            ])
            .collect::<Vec<_>>();
        debug!("Equations for resolution from {from:?} to {to:?} are:");
        for eq in equations.iter() {
            debug!("  {eq}");
        }
        let mut results = solve(&equations, &source, |&local| {
            if local == target {
                Either::Left(())
            } else {
                Either::Right(local)
            }
        });
        assert!(results.len() <= 1);
        let ret = results.pop();
        if let Some(res) = ret.as_ref() {
            debug!("Resolved to {}", res.replace_base(DisplayViaDebug(target)));
        } else {
            debug!("No resolution found");
        }
        ret
    }

}
