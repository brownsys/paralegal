use crate::{
    mir::{Location, ProjectionElem, Field},
    rust::{rustc_hir::def_id::DefId, rustc_index::vec::IndexVec},
    HashMap, HashSet,
    utils::{AsFnAndArgs, LocationExt},
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

#[derive(Hash, Eq, PartialEq, Debug)]
struct Dependency {
    target: Target,
    target_term: algebra::Term<TargetPlace, Field>
}

#[derive(Hash, Eq, PartialEq, Debug)]
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
        let body = flow_analysis
            .analysis
            .body;
        let calls = body
            .basic_blocks()
            .iter_enumerated()
            .filter_map(|(bb, bbdat)| {
                let (function, simple_args, _) = bbdat.terminator().as_fn_and_args().ok()?;
                let bbloc = body.terminator_loc(bb);
                let arguments = 
                    simple_args.into_iter()
                        .map(|arg| if let Some(arg) = arg {
                            let ana = flow_analysis.state_at(bbloc);
                            ana.deps(arg).map(|&(dep_loc, dep_place)| {
                                let target = if dep_loc.is_real(body) {
                                    Target::Call(dep_loc)
                                } else {
                                    Target::Argument(dep_loc.statement_index as u16 - 1)
                                };
                                let (_, target_args, target_ret) = 
                                    body.stmt_at(dep_loc)
                                        .right()
                                        .unwrap()
                                        .as_fn_and_args()
                                        .unwrap();
                                let target_place = 
                                    target_args.into_iter()
                                        .enumerate()
                                        .filter_map(|(idx, p)| (p?.local == dep_place.local).then(|| TargetPlace::Argument(ArgumentIndex::from_usize(idx))))
                                        .next()
                                        .unwrap_or_else(|| {
                                            assert!(target_ret.unwrap().0.local == dep_place.local);
                                            TargetPlace::Return
                                        });
                                let target_term = place_resolver.resolve(arg, dep_place).replace_base(target_place);
                                Dependency {target_term, target}
                            }).collect()
                        } else {
                            Dependencies::default()
                        })
                        .collect();
                Some((bbloc, Call {
                    function,
                    arguments
                }))
            })
            .collect();
        Self { calls }
    }
}