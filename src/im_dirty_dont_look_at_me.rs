use std::rc::Rc;

use crate::{mir, serde, HashMap, Symbol};

use flowistry::indexed::{impls::LocationIndex, IndexMatrix, IndexSetImpl, IndexedValue};
use serde::Serialize;

#[derive(PartialEq, Eq, Hash)]
struct SymbolDef(Symbol);

impl<'de> serde::Deserialize<'de> for SymbolDef {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        String::deserialize(deserializer).map(|s| SymbolDef(Symbol::intern(&s)))
    }
}

impl Serialize for SymbolDef {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.as_str().serialize(serializer)
    }
}

fn bbref_to_usize(r: &mir::BasicBlock) -> usize {
    r.as_usize()
}

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(remote = "mir::BasicBlock")]
struct BasicBlockDef {
    #[serde(getter = "bbref_to_usize")]
    private: usize,
}

impl Into<mir::BasicBlock> for BasicBlockDef {
    fn into(self) -> mir::BasicBlock {
        mir::BasicBlock::from_usize(self.private)
    }
}

#[derive(serde::Serialize, Eq, PartialEq, Hash, serde::Deserialize)]
struct LocationDef {
    #[serde(with = "BasicBlockDef")]
    pub block: mir::BasicBlock,
    pub statement_index: usize,
}

#[derive(serde::Serialize, serde::Deserialize)]
struct BitSetDef<T> {
    domain_size: usize,
    words: Vec<u64>,
    marker: std::marker::PhantomData<T>,
}

fn serialize_from_rc<T: serde::Serialize, S: serde::Serializer>(
    this: &Rc<T>,
    s: S,
) -> Result<S::Ok, S::Error> {
    (**this).serialize(s)
}
fn deserialize_into_rc<'de, D, T: serde::Deserialize<'de>>(d: D) -> Result<Rc<T>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    T::deserialize(d).map(Rc::new)
}

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(bound(
    serialize = "R:std::cmp::Eq + std::hash::Hash + serde::Serialize, Domain: serde::Serialize",
    deserialize = "Domain: serde::Deserialize<'de>, R: serde::Deserialize<'de> + std::cmp::Eq + std::hash::Hash"
))]
struct IndexMatrixDef<R, Index, Domain> {
    matrix: HashMap<R, BitSetDef<Index>>,
    empty_set: BitSetDef<Index>,
    #[serde(
        serialize_with = "serialize_from_rc",
        deserialize_with = "deserialize_into_rc"
    )]
    col_domain: Rc<Domain>,
}

pub type SerializableGraphImpl = HashMap<mir::Location, IndexMatrix<Symbol, mir::Location>>;
type SerializableGraphProxy =
    HashMap<LocationDef, IndexMatrixDef<SymbolDef, LocationIndex, LocationDef>>;

pub struct SerializableNonTransitiveGraph(pub SerializableGraphImpl);

impl<'de> serde::Deserialize<'de> for SerializableNonTransitiveGraph {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        <SerializableGraphProxy as serde::Deserialize>::deserialize(deserializer)
            .map(|p| SerializableNonTransitiveGraph(unsafe { std::mem::transmute(p) }))
    }
}

impl Serialize for SerializableNonTransitiveGraph {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let r: &SerializableGraphProxy = unsafe { std::mem::transmute(&self.0) };
        r.serialize(serializer)
    }
}
