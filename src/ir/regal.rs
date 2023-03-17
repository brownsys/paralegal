use flowistry::{
    extensions::RecurseSelector,
    mir::{borrowck_facts, utils::BodyExt},
};

use crate::{
    mir,
    mir::{Field, Location, ProjectionElem},
    rust::{
        rustc_hir::{def_id::DefId, BodyId},
        rustc_index::vec::IndexVec,
    },
    utils::{outfile_pls, AsFnAndArgs, DisplayViaDebug, LocationExt},
    Either, HashMap, HashSet, TyCtxt,
};

use std::{
    cell::RefCell,
    fmt::{Display, Write},
    rc::Rc,
};

newtype_index!(
    pub struct ArgumentIndex {
        DEBUG_FORMAT = "arg{}"
    }
);

impl Display for ArgumentIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "a{}", self.as_usize())
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum TargetPlace {
    Return,
    Argument(ArgumentIndex),
}

pub type TargetTerm = algebra::Term<TargetPlace, DisplayViaDebug<Field>>;

#[derive(Hash, Eq, PartialEq, Debug, Clone)]
pub struct Dependency<L> {
    pub target: Target<L>,
    pub target_term: TargetTerm,
}

impl <L> Dependency<L> {
    pub fn map_locations<L0, F: FnMut(&L) -> L0>(&self, f: F) -> Dependency<L0> {
        Dependency {
            target: self.target.map_location(f),
            target_term: self.target_term.clone(),
        }
    }
}

impl<L: Display> Display for Dependency<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} @ {}", self.target, self.target_term)
    }
}

#[derive(Hash, Eq, PartialEq, Debug, Copy, Clone)]
pub enum Target<L> {
    Call(L),
    Argument(ArgumentIndex),
}

impl <L> Target<L> {
    pub fn map_location<L0, F: FnMut(&L) -> L0>(&self, mut f: F) -> Target<L0> {
        match self {
            Target::Argument(a) => Target::Argument(*a),
            Target::Call(l) => Target::Call(f(l))
        }
    }
}

impl<L: Display> Display for Target<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Target::Call(loc) => write!(f, "{loc}"),
            Target::Argument(a) => a.fmt(f),
        }
    }
}

type Dependencies<L> = HashSet<Dependency<L>>;

#[derive(Debug)]
pub struct Call<L> {
    pub function: DefId,
    pub arguments: IndexVec<ArgumentIndex, Dependencies<L>>,
}

impl <L> Call<L> {
    pub fn map_locations<L0: std::hash::Hash + Eq, F: FnMut(&L) -> L0>(&self, mut f: F) -> Call<L0> {
        let arguments = 
            self.arguments.iter().map(|set| set.iter().map(|d| d.map_locations(&mut f)).collect()).collect();
        Call {
            function: self.function, arguments
        }
    }

    pub fn flat_map_dependencies<L0: Eq + std::hash::Hash, F: FnMut(&Dependency<L>) -> I, I: Iterator<Item=Dependency<L0>>>(&self, mut f: F) -> Call<L0>
    {
        Call {
            function: self.function, arguments: self.arguments.iter().map(|a| a.iter().flat_map(&mut f).collect()).collect()
        }
    }

    pub fn expand_arguments<F: FnMut(ArgumentIndex, &TargetTerm) -> I, I: Iterator<Item=Dependency<L>>>(&self, mut f: F) -> Self 
    where L: Eq + std::hash::Hash + Clone
    {
        self.flat_map_dependencies(|d| if let Target::Argument(u) = d.target {
            Either::Right(f(u, &d.target_term))
        } else {
            let c : Dependency<L> = d.clone();
            Either::Left(std::iter::once(c))
        }.into_iter())
    }
}

impl<L: Display> Display for Call<L> {
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
pub struct Body<L> {
    pub calls: HashMap<L, Call<L>>,
    pub return_state: Dependencies<L>,
}

impl<L> Body<L> {
    pub fn calls(&self) -> &HashMap<L, Call<L>> {
        &self.calls
    }

    pub fn at(&self, l: &L) -> Option<&Call<L>>
    where
        L: Eq + std::hash::Hash,
    {
        self.calls.get(l)
    }
}

impl<L: Display + Ord> Display for Body<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ordered = self.calls.iter().collect::<Vec<_>>();
        ordered.sort_by_key(|t| t.0);
        for (loc, call) in ordered {
            writeln!(f, "{:<6}: {}", format!("{}", loc), call)?
        }
        Ok(())
    }
}

pub struct MemoizingConstructor<'tcx, 'g> {
    tcx: TyCtxt<'tcx>,
    gli: GLI<'g>,
    memoizer: RefCell<HashMap<BodyId, Rc<Body<DisplayViaDebug<Location>>>>>,
}

struct NeverInline;

impl RecurseSelector for NeverInline {
    fn is_selected<'tcx>(&self, _tcx: TyCtxt<'tcx>, _tk: &mir::TerminatorKind<'tcx>) -> bool {
        false
    }
}

pub fn compute_from_body_id(body_id: BodyId, tcx: TyCtxt, gli: GLI) -> Body<DisplayViaDebug<Location>> {
    let hir = tcx.hir();
    let target_name = hir.name(hir.body_owner(body_id));
    let local_def_id = tcx.hir().body_owner_def_id(body_id);
    let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, local_def_id);
    let body = body_with_facts.simplified_body();
    let flow =
        df::compute_flow_internal(tcx, gli, body_id, body_with_facts, &NeverInline);
    mir::pretty::write_mir_fn(
        tcx,
        body,
        &mut |_, _| Ok(()),
        &mut outfile_pls(&format!("{}.mir", target_name)).unwrap(),
    )
    .unwrap();
    let ref mut states_out = outfile_pls(&format!("{}.df", target_name)).unwrap();
    for l in body.all_locations() {
        writeln!(states_out, "{l:?}: {}", flow.state_at(l)).unwrap();
    }
    let place_resolver = algebra::PlaceResolver::construct(tcx, body);
    let r = Body::construct(&flow, &place_resolver);
    let mut out = outfile_pls(&format!("{}.regal", target_name)).unwrap();
    use std::io::Write;
    write!(&mut out, "{}", r).unwrap();
    r
}

impl<'tcx, 'g> MemoizingConstructor<'tcx, 'g> {
    pub fn new(tcx: TyCtxt<'tcx>, gli: GLI<'g>) -> Self {
        Self {
            tcx,
            gli,
            memoizer: Default::default(),
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn gli(&self) -> GLI<'g> {
        self.gli
    }

    pub fn get(&self, body_id: BodyId) -> Rc<Body<DisplayViaDebug<Location>>> {
        if let Some(b) = self.memoizer.borrow().get(&body_id) {
            return b.clone();
        }
        let r = compute_from_body_id(body_id, self.tcx(), self.gli());
        let rc = Rc::new(r);
        self.memoizer.borrow_mut().insert(body_id, rc.clone());
        rc
    }
}

use crate::ana::{algebra, df};

use super::GLI;

impl Body<DisplayViaDebug<Location>> {
    pub fn construct(
        flow_analysis: &df::FlowResults<'_, '_, '_>,
        place_resolver: &algebra::PlaceResolver,
    ) -> Self {
        let body = flow_analysis.analysis.body;
        let dependencies_for = |location : DisplayViaDebug<_>, arg| {
            let ana = flow_analysis.state_at(*location);
            ana.deps(arg)
                .flat_map(|&(dep_loc, _dep_place)| {
                    let dep_loc = DisplayViaDebug(dep_loc);
                    let (target, places) = if dep_loc.is_real(body) {
                        let (_, target_args, target_ret) = body
                            .stmt_at(*dep_loc)
                            .right()
                            .unwrap()
                            .as_fn_and_args()
                            .unwrap();

                        let places = target_args
                            .into_iter()
                            .enumerate()
                            .filter_map(|(idx, p)| {
                                Some((TargetPlace::Argument(ArgumentIndex::from_usize(idx)), p?))
                            })
                            .chain(std::iter::once({
                                let p = target_ret.unwrap().0;
                                (TargetPlace::Return, p)
                            }));
                        (Target::Call(dep_loc), Either::Left(places))
                    } else {
                        (
                            Target::Argument(ArgumentIndex::from_usize(dep_loc.statement_index - 1)),
                            Either::Right(std::iter::once((
                                TargetPlace::Return,
                                mir::Local::from_usize(dep_loc.statement_index).into(),
                            ))),
                        )
                    };
                    places.into_iter().filter_map(
                        move |(abstract_target_place, concrete_target_place)| {
                            let target_term = place_resolver
                                .try_resolve(arg, concrete_target_place)?
                                .replace_base(abstract_target_place);
                            Some(Dependency {
                                target_term,
                                target,
                            })
                        },
                    )
                })
                .collect()
        };
        let calls = body
            .basic_blocks()
            .iter_enumerated()
            .filter_map(|(bb, bbdat)| {
                let (function, simple_args, _) = bbdat.terminator().as_fn_and_args().ok()?;
                let bbloc = DisplayViaDebug(body.terminator_loc(bb));
                let arguments = 
                    IndexVec::from_raw(
                    simple_args
                    .into_iter()
                    .map(|arg| {
                        arg.map_or_else(Dependencies::default, |a| dependencies_for(bbloc, a))
                    })
                    .collect());
                Some((
                    bbloc,
                    Call {
                        function,
                        arguments,
                    },
                ))
            })
            .collect();
        let return_state = body
            .all_returns()
            .map(DisplayViaDebug)
            .flat_map(|loc| dependencies_for(loc, mir::Place::return_place()).clone().into_iter())
            .collect();
        Self {
            calls,
            return_state,
        }
    }
}
