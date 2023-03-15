use crate::{
    mir::{Field, Location, ProjectionElem},
    rust::{rustc_hir::def_id::DefId, rustc_index::vec::IndexVec},
    utils::{AsFnAndArgs, LocationExt},
    HashMap, HashSet, Either, mir
};

use std::fmt::{Display, Write};

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
    target_term: algebra::Term<TargetPlace, algebra::DisplayViaDebug<Field>>,
}

impl Display for Dependency {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} @ {}", self.target, self.target_term)
    }
}

#[derive(Hash, Eq, PartialEq, Debug, Copy, Clone)]
enum Target {
    Call(Location),
    Argument(u16),
}

impl Display for Target {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Target::Call(loc) => write!(f, "{loc:?}"),
            Target::Argument(a) => write!(f, "a{a}"),
        }
    }
}

type Dependencies = HashSet<Dependency>;

#[derive(Debug)]
struct Call {
    function: DefId,
    arguments: IndexVec<ArgumentIndex, Dependencies>,
}

impl Display for Call {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('(')?;
        let mut first = true;
        for arg in self.arguments.iter() {
            if first {
                first = false;
            } else {
                f.write_str(", ")?;
            }
            f.write_char('{')?;
            let mut first_dep = true;
            for dep in arg {
                if first_dep {
                    first_dep = false;
                } else {
                    f.write_str(", ")?;
                }
                write!(f, "{dep}")?;
            }
            f.write_char('}')?;
        }
        write!(f, ")   {:?}", self.function)?;
        Ok(())
    }
}

#[derive(Debug)]
pub struct Body {
    calls: HashMap<Location, Call>,
}

impl Display for Body {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ordered = self.calls.iter().collect::<Vec<_>>();
        ordered.sort_by_key(|t| t.0);
        for (loc, call) in ordered {
            writeln!(f, "{:<6}: {}", format!("{:?}", loc), call)?
        }
        Ok(())
    }
}

use crate::ana::{algebra, df};

impl Body {
    pub fn construct(
        flow_analysis: &df::FlowResults<'_, '_, '_>,
        place_resolver: &algebra::PlaceResolver,
    ) -> Self {
        let body = flow_analysis.analysis.body;
        let calls = body
            .basic_blocks()
            .iter_enumerated()
            .filter_map(|(bb, bbdat)| {
                let (function, simple_args, _) = bbdat.terminator().as_fn_and_args().ok()?;
                let bbloc = body.terminator_loc(bb);
                let arguments = simple_args
                    .into_iter()
                    .map(|arg| {
                        if let Some(arg) = arg {
                            let ana = flow_analysis.state_at(bbloc);
                            ana.deps(arg)
                                .flat_map(|&(dep_loc, dep_place)| {
                                    let (target, places) = if dep_loc.is_real(body) {

                                    let (_, target_args, target_ret) = body
                                        .stmt_at(dep_loc)
                                        .right()
                                        .unwrap()
                                        .as_fn_and_args()
                                        .unwrap();
                                    
                                    let places = target_args
                                        .into_iter()
                                        .enumerate()
                                        .filter_map(|(idx, p)|
                                            Some((
                                                TargetPlace::Argument(
                                                    ArgumentIndex::from_usize(idx),
                                                ),
                                                p?,
                                            ))
                                        )
                                        .chain(std::iter::once({
                                            let p = target_ret.unwrap().0;
                                            (TargetPlace::Return, p)
                                        }));
                                        (Target::Call(dep_loc), Either::Left(places))
                                    } else {
                                        (Target::Argument(dep_loc.statement_index as u16 - 1), 
                                        Either::Right(std::iter::once((TargetPlace::Return, mir::Local::from_usize(dep_loc.statement_index).into()))))
                                    };
                                    places.into_iter()
                                        .filter_map(move |(abstract_target_place, concrete_target_place)| {
                                            let target_term = place_resolver
                                                .try_resolve(arg, concrete_target_place)?
                                                .replace_base(abstract_target_place);
                                            Some(Dependency {
                                                target_term,
                                                target,
                                            })
                                        })
                                })
                                .collect()
                        } else {
                            Dependencies::default()
                        }
                    })
                    .collect();
                Some((
                    bbloc,
                    Call {
                        function,
                        arguments,
                    },
                ))
            })
            .collect();
        Self { calls }
    }
}
