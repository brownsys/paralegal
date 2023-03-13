use crate::{
    mir::{Location, ProjectionElem},
    rust::{rustc_hir::def_id::DefId, rustc_index::vec::IndexVec},
    HashMap, HashSet,
};

newtype_index!(
    pub struct ArgumentIndex {
        DEBUG_FORMAT = "arg{}"
    }
);

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum ProjElem {
    Ref,
    FromMir(ProjectionElem<(), ()>),
}

#[derive(Eq, PartialEq, Clone, Copy, Hash, Debug)]
pub enum Delta {
    Positive,
    Negative,
}

impl std::ops::Not for Delta {
    type Output = Self;
    fn not(self) -> Self::Output {
        match self {
            Delta::Negative => Delta::Positive,
            Delta::Positive => Delta::Negative,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Projections(Vec<ProjElem>);

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct ProjectionDelta {
    delta: Delta,
    projections: Projections,
}

impl Default for ProjectionDelta {
    fn default() -> Self {
        Self {
            delta: Delta::Positive,
            projections: Projections(vec![]),
        }
    }
}

impl Projections {
    pub fn apply(&mut self, delta: &ProjectionDelta) {
        self.apply_in_pieces(delta.delta, &delta.projections)
    }
    fn apply_in_pieces(&mut self, delta: Delta, projections: &Projections) {
        match delta {
            Delta::Positive => self.0.extend(projections.0.iter().cloned()),
            Delta::Negative => self
                .0
                .drain(..projections.0.len())
                .zip(projections.0.iter())
                .for_each(|(old, new)| assert_eq!(&old, new)),
        }
    }
}

impl ProjectionDelta {
    pub fn apply(&mut self, other: &ProjectionDelta) {
        match self.delta {
            Delta::Positive => self.projections.apply(other),
            Delta::Negative => self
                .projections
                .apply_in_pieces(!other.delta, &other.projections),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum TargetPlace {
    Return,
    Argument(ArgumentIndex),
}

struct Dependency {
    target: Target,
    target_place: TargetPlace,
    projection_delta: ProjectionDelta,
}

enum Target {
    Call(Location),
    Argument(u16),
}

type Dependencies = HashSet<Dependency>;

struct Call {
    function: DefId,
    arguments: IndexVec<ArgumentIndex, Dependencies>,
}

struct Body {
    calls: HashMap<Location, Call>,
}

use crate::ana::{df, algebra};

impl Body {
    fn construct(flow_analysis: df::FlowResults<'_, '_, '_>, place_resolver: algebra::PlaceResolver) -> Self {

    }
}