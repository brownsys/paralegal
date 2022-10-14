use std::{borrow::Cow, rc::Rc};

use flowistry::{
    indexed::{impls::LocationDomain, DefaultDomain, IndexMatrix, IndexSet, RefSet},
    mir::utils::PlaceExt,
};
use serde::Deserialize;

use crate::{
    ana::extract_places,
    mir,
    rust::TyCtxt,
    serde::{Serialize, Serializer},
    Either, HashMap, HashSet, Symbol,
};

fn bbref_to_usize(r: &mir::BasicBlock) -> usize {
    r.as_usize()
}

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(remote = "mir::BasicBlock")]
struct BasicBlockProxy {
    #[serde(getter = "bbref_to_usize")]
    private: usize,
}

impl Into<mir::BasicBlock> for BasicBlockProxy {
    fn into(self) -> mir::BasicBlock {
        mir::BasicBlock::from_usize(self.private)
    }
}

#[derive(serde::Serialize, Eq, PartialEq, Hash, serde::Deserialize)]
struct LocationProxy {
    #[serde(with = "BasicBlockProxy")]
    pub block: mir::BasicBlock,
    pub statement_index: usize,
}

impl From<mir::Location> for LocationProxy {
    fn from(l: mir::Location) -> Self {
        Self {
            block: l.block,
            statement_index: l.statement_index,
        }
    }
}

impl Into<mir::Location> for LocationProxy {
    fn into(self) -> mir::Location {
        let Self {
            block,
            statement_index,
        } = self;
        mir::Location {
            block,
            statement_index,
        }
    }
}

pub struct BodyProxy(pub Vec<(mir::Location, String, HashSet<Symbol>)>);

impl Serialize for BodyProxy {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0
            .iter()
            .map(|(l, s, h)| {
                (
                    (*l).into(),
                    s,
                    h.iter().map(|s| s.as_str()).collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<(LocationProxy, _, _)>>()
            .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for BodyProxy {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        <Vec<(LocationProxy, String, Vec<SymbolProxy>)> as Deserialize<'de>>::deserialize(
            deserializer,
        )
        .map(|v| {
            v.into_iter()
                .map(|(l, s, vs)| (l.into(), s, vs.into_iter().map(|s| s.into()).collect()))
                .collect()
        })
        .map(BodyProxy)
    }
}
fn iter_stmts<'a, 'tcx>(
    b: &'a mir::Body<'tcx>,
) -> impl Iterator<
    Item = (
        mir::Location,
        Either<&'a mir::Statement<'tcx>, &'a mir::Terminator<'tcx>>,
    ),
> {
    b.basic_blocks()
        .iter_enumerated()
        .flat_map(|(block, bbdat)| {
            bbdat
                .statements
                .iter()
                .enumerate()
                .map(move |(statement_index, stmt)| {
                    (
                        mir::Location {
                            block,
                            statement_index,
                        },
                        Either::Left(stmt),
                    )
                })
                .chain(std::iter::once((
                    mir::Location {
                        block,
                        statement_index: bbdat.statements.len(),
                    },
                    Either::Right(bbdat.terminator()),
                )))
        })
}

impl<'tcx> From<&mir::Body<'tcx>> for BodyProxy {
    fn from(body: &mir::Body<'tcx>) -> Self {
        Self(
            iter_stmts(body)
                .map(|(loc, stmt)| {
                    (
                        loc,
                        stmt.either(|s| format!("{:?}", s.kind), |t| format!("{:?}", t.kind)),
                        extract_places(loc, body, false)
                            .into_iter()
                            .map(|p| Symbol::intern(&format!("{p:?}")))
                            .collect(),
                    )
                })
                .collect::<Vec<_>>(),
        )
    }
}

impl BodyProxy {
    pub fn from_body_with_normalize<'tcx>(
        body: &mir::Body<'tcx>,
        aliases: &flowistry::mir::aliases::Aliases<'_, 'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        Self(
            iter_stmts(body)
                .map(|(loc, stmt)| {
                    (
                        loc,
                        stmt.either(|s| format!("{:?}", s.kind), |t| format!("{:?}", t.kind)),
                        extract_places(loc, body, false)
                            .iter()
                            .flat_map(|place| {
                                std::iter::once(*place).chain(
                                    place
                                        .refs_in_projection()
                                        .into_iter()
                                        .map(|t| mir::Place::from_ref(t.0, tcx)),
                                )
                            })
                            .map(|p| Symbol::intern(&format!("{p:?}")))
                            .collect(),
                    )
                })
                .collect::<Vec<_>>(),
        )
    }
}

struct SymbolProxy(Symbol);

impl<'de> serde::Deserialize<'de> for SymbolProxy {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        String::deserialize(deserializer).map(|s| Self(Symbol::intern(&s)))
    }
}

impl Serialize for SymbolProxy {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.as_str().serialize(serializer)
    }
}

impl From<Symbol> for SymbolProxy {
    fn from(sym: Symbol) -> Self {
        Self(sym)
    }
}

impl Into<Symbol> for SymbolProxy {
    fn into(self) -> Symbol {
        self.0
    }
}

#[derive(Serialize, Deserialize)]
struct LocationDomainProxy {
    domain: Vec<LocationProxy>,
    #[serde(with = "BasicBlockProxy")]
    arg_block: mir::BasicBlock,
    real_locations: usize,
}

#[derive(Serialize, Deserialize)]
pub struct NonTransitiveGraphProxy {
    domain: LocationDomainProxy,
    matrices: Vec<(LocationProxy, Vec<(SymbolProxy, HashSet<LocationProxy>)>)>,
}

impl<'tcx> From<&crate::ana::NonTransitiveGraph<'tcx>> for NonTransitiveGraphProxy {
    fn from(g: &crate::ana::NonTransitiveGraph<'tcx>) -> Self {
        use flowistry::indexed::IndexedDomain;
        let a_domain = &g.values().next().expect("Empty graphs").col_domain;
        let domain = LocationDomainProxy {
            domain: a_domain
                .as_vec()
                .raw
                .iter()
                .map(|l| LocationProxy::from(*l))
                .collect(),
            arg_block: a_domain.arg_block(),
            real_locations: a_domain.num_real_locations(),
        };
        Self {
            domain,
            matrices: g
                .iter()
                .map(|(k, v)| {
                    (
                        (*k).into(),
                        v.rows()
                            .map(|(i, m)| {
                                (
                                    Symbol::intern(&format!("{:?}", i)).into(),
                                    m.iter().map(|l| (*l).into()).collect(),
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
        }
    }
}

pub type SerializableNonTransitiveGraph =
    HashMap<mir::Location, IndexMatrix<Symbol, mir::Location>>;

impl Into<SerializableNonTransitiveGraph> for NonTransitiveGraphProxy {
    fn into(self) -> SerializableNonTransitiveGraph {
        let Self { domain, matrices } = self;
        let LocationDomainProxy {
            domain,
            arg_block,
            real_locations,
        } = domain;
        let dom = Rc::new(LocationDomain::from_raw(
            DefaultDomain::new(domain.into_iter().map(|l| l.into()).collect()),
            arg_block,
            real_locations,
        ));
        matrices
            .into_iter()
            .map(|(l, v)| {
                (l.into(), {
                    let mut m = IndexMatrix::new(&dom);
                    for (s, idxes) in v.into_iter() {
                        let sym = s.into();
                        for idx in idxes.into_iter() {
                            m.insert(sym, <LocationProxy as Into<mir::Location>>::into(idx));
                        }
                    }
                    m
                })
            })
            .collect()
    }
}
