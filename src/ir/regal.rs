use std::collections::HashSet;

use crate::{
    mir::{Location, ProjectionElem},
    rust::{rustc_hir::def_id::DefId, rustc_index::vec::IndexVec},
    HashMap,
};

newtype_index!(
    pub struct ArgumentIndex {
        DEBUG_FORMAT = "arg{}"
    }
);

enum ProjElem {
    Ref,
    FromMir(ProjectionElem<(), ()>),
}

type ProjectionDelta = Vec<ProjElem>;

enum TargetPlace {
    Return,
    Argument(ArgumentIndex),
}

struct Dependency {
    target_call: Location,
    target_place: TargetPlace,
    projection_delta: ProjectionDelta,
}

type Dependencies = HashSet<Dependency>;

struct Call {
    function: DefId,
    arguments: IndexVec<ArgumentIndex, Dependencies>,
}

struct Body {
    calls: HashMap<Location, Call>,
}
