use std::{cell::RefCell, rc::Rc};

use syn::token::Override;

use crate::{
    mir,
    rust::{
        rustc_index::vec::{Idx, IndexVec},
        rustc_mir_dataflow::JoinSemiLattice,
    },
    ty, HashSet,
};

// #[derive(PartialEq, Eq)]
// pub struct Value<'tcx, A>(Rc<RefCell<ValueT<'tcx, A>>>);

// impl <'tcx, A> Value<'tcx, A> {
//     pub fn new(t: ValueT<'tcx, A>) -> Self {
//         Self(Rc::new(RefCell::new(t)))
//     }

//     pub fn deep_clone(&self) -> Self {
//         unimplemented!()
//     }

// }

pub type Fields<'tcx, A> = IndexVec<mir::Field, Value<'tcx, A>>;

// impl <'tcx, A : JoinSemiLattice + Default> JoinSemiLattice for Value<'tcx, A> {
//     fn join(&mut self, other: &Self) -> bool {
//         let other = other.0.borrow();
//         self.0.borrow_mut().join(&other)
//     }
// }

#[derive(PartialEq, Eq)]
pub enum Value<'tcx, A> {
    Abstract(A),
    Struct(Fields<'tcx, A>, Option<A>),
    Tuple(IndexVec<usize, Value<'tcx, A>>, Option<A>),
    Ref(HashSet<mir::Place<'tcx>>),
    Uninit,
    Override(A),
}

impl<'tcx, A: JoinSemiLattice> Value<'tcx, A> {
    pub fn override_(
        &mut self,
        projections: &ty::List<mir::PlaceElem>,
        dep: A,
    ) -> Option<HashSet<mir::Place<'tcx>>> {
        let mut running = self;
        use mir::ProjectionElem as P;
        use Value as V;
        for prj in projections {
            match (running, prj) {
                (V::Ref(places), P::Deref) => Some(),
            }
        }
        if let Value::Override(o) = running {
            o.join(&dep);
        } else {
            *running = Value::Override(dep);
        }
        None
    }
}

impl<'tcx, A> Value<'tcx, A> {
    pub fn deep_clone(&self) -> Self {
        unimplemented!()
    }
}

fn join_structure<'tcx, A: JoinSemiLattice + Default, I: Idx>(
    fields: &mut IndexVec<I, Value<'tcx, A>>,
    general_val: &mut Option<A>,
    other_fields: &IndexVec<I, Value<'tcx, A>>,
    other_general_val: &Option<A>,
) -> bool {
    let changed = false;
    other_fields.iter_enumerated().for_each(|(idx, f)| {
        fields.ensure_contains_elem(idx, || Value::Uninit);
        changed |= fields[idx].join(f);
    });
    if let Some(other) = other_general_val.as_ref() {}
    changed
}

impl<'tcx, A: JoinSemiLattice + Default> JoinSemiLattice for Value<'tcx, A> {
    fn join(&mut self, other: &Self) -> bool {
        use Value::*;
        let mut changed = false;
        match (self, other) {
            (_, Uninit) | (Override(..), _) => (),
            (_, Override(other)) | (_, Abstract(other)) => {
                let my = match self {
                    Tuple(_, my) | Struct(_, my) => my.get_or_insert_with(A::default),
                    Abstract(my) => my,
                    Uninit => {
                        *self = Abstract(A::default());
                        match self {
                            Abstract(a) => a,
                            _ => unreachable!(),
                        }
                    }
                    _ => unreachable!(),
                };
                changed = my.join(other);
            }
            (Abstract(my), other) => {
                let moved = std::mem::replace(my, A::default());
                *self = other.deep_clone();
                match self {
                    Tuple(_, general) | Struct(_, general) => {
                        general.get_or_insert_with(A::default).join(&moved)
                    }
                    _ => unreachable!(),
                };
                changed = true;
            }
            (Uninit, _) => {
                *self = other.deep_clone();
                changed = true
            }
            (Ref(refs), Ref(others)) => others.iter().for_each(|r| changed |= refs.insert(*r)),
            (Struct(fields, val), Struct(other_fields, other_val)) => {
                changed |= join_structure(fields, val, other_fields, other_val)
            }
            (Tuple(tfields, tval), Tuple(other_tfields, other_tval)) => {
                changed |= join_structure(tfields, tval, other_tfields, other_tval)
            }

            _ => unreachable!(),
        };
        changed
    }
}

#[derive(PartialEq, Eq)]
pub struct Memory<'tcx, A> {
    mem: IndexVec<mir::Local, Value<'tcx, A>>,
}

impl<'tcx, A: JoinSemiLattice + Default> JoinSemiLattice for Memory<'tcx, A> {
    fn join(&mut self, other: &Self) -> bool {
        assert_eq!(self.mem.len(), other.mem.len());
        let mut has_changed = false;
        self.mem
            .iter_mut()
            .zip(other.mem.iter())
            .for_each(|(target, source)| has_changed |= target.join(source));
        has_changed
    }
}

impl<'tcx, A: JoinSemiLattice> Memory<'tcx, A> {
    fn override_(&mut self, place: mir::Place<'tcx>, dependency: A) {
        while let Some(new_targets) = self.mem[place.local].override_(place.projection, dependency)
        {
            for target in new_targets {
                self.override_(target, dependency);
            }
        }
    }
}
