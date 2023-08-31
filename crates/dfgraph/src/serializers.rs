//! [`serde`] serializers, most used for JSON debugging output in [`crate::dbg`].
//!
//! The proxy structs are foreign serializers for their non-proxy counterparts,
//! see <https://serde.rs/remote-derive.html> for more information. As a naming
//! convention `<name>Proxy` is used to (de)serialize `<name>` e.g.
//! [`BasicBlockProxy`] (de)serializes a [`mir::BasicBlock`].
//!
//! Be aware that in some cases serialization is not bidirectional (usually if
//! there is a lifetime parameter in the serialized type). For instance
//! [`GlobalLocation`] can be serialized, but only a [`RawGlobalLocation`] can
//! be deserialized.
//!
//! Some types (such as [`mir::Body`]) first have to be explicitly transformed
//! into the respective proxy type. In the case of [`mir::Body`] this can be
//! done with [`BodyProxy::from_body_with_normalize`]
use serde::Deserialize;

use crate::HashSet;
use rustc_hir::{self as hir, def_id};
use rustc_middle::mir;
use rustc_span::Symbol;
use serde::{Serialize, Serializer};

// use crate::{
//     ir::{CallDeps, CallOnlyFlow, GlobalLocation, RawGlobalLocation},
//     utils::{extract_places, read_places_with_provenance, DfppBodyExt},
// };

fn bbref_to_usize(r: &mir::BasicBlock) -> usize {
    r.as_usize()
}

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(remote = "mir::BasicBlock")]
struct BasicBlockProxy {
    #[serde(getter = "bbref_to_usize")]
    private: usize,
}

impl From<BasicBlockProxy> for mir::BasicBlock {
    fn from(proxy: BasicBlockProxy) -> mir::BasicBlock {
        mir::BasicBlock::from_usize(proxy.private)
    }
}

#[derive(serde::Serialize, Eq, PartialEq, Hash, serde::Deserialize)]
pub struct LocationProxy {
    #[serde(with = "BasicBlockProxy")]
    pub block: mir::BasicBlock,
    pub statement_index: usize,
}

pub mod ser_loc {
    //! Serialization of locations, bundled into a `mod` so that you can use it
    //! like
    //! [`#[serde(with="ser_loc")]`](https://serde.rs/field-attrs.html#with)
    use super::mir;
    use serde::{Deserialize, Serialize};

    pub fn deserialize<'de, D>(deserializer: D) -> Result<mir::Location, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        super::LocationProxy::deserialize(deserializer).map(|s| s.into())
    }

    pub fn serialize<S>(s: &mir::Location, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        super::LocationProxy::from(*s).serialize(serializer)
    }
}

impl From<mir::Location> for LocationProxy {
    fn from(l: mir::Location) -> Self {
        Self {
            block: l.block,
            statement_index: l.statement_index,
        }
    }
}

impl From<LocationProxy> for mir::Location {
    fn from(proxy: LocationProxy) -> mir::Location {
        let LocationProxy {
            block,
            statement_index,
        } = proxy;
        mir::Location {
            block,
            statement_index,
        }
    }
}

/// A serializable version of a `mir::Body`.
///
/// Be aware that this transports less information than the actual `mir::Body`.
/// It records for each [`mir::Location`] a string representation of the
/// statement or terminator at that location and a set of [`mir::Place`]s that
/// are mentioned in the statement/terminator, also represented as strings
/// (though using the efficient, interned [`Symbol`]s).
///
/// Construct one with [`Self::from_body_with_normalize`].
#[derive(Debug)]
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
pub struct SymbolProxy(Symbol);

pub mod ser_sym {
    //! Serialization of [`Symbol`]s, bundled into a `mod` so that you can use it
    //! like
    //! [`#[serde(with="ser_sym")]`](https://serde.rs/field-attrs.html#with)
    use crate::Symbol;
    use serde::{Deserialize, Serialize};

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Symbol, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        super::SymbolProxy::deserialize(deserializer).map(|s| s.into())
    }

    pub fn serialize<S>(s: &Symbol, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        super::SymbolProxy::from(*s).serialize(serializer)
    }
}

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

impl From<SymbolProxy> for Symbol {
    fn from(proxy: SymbolProxy) -> Symbol {
        proxy.0
    }
}

#[derive(Serialize, Deserialize)]
struct LocationDomainProxy {
    domain: Vec<LocationProxy>,
    #[serde(with = "BasicBlockProxy")]
    arg_block: mir::BasicBlock,
    real_locations: usize,
}

fn item_local_id_as_u32(i: &hir::ItemLocalId) -> u32 {
    i.as_u32()
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "hir::ItemLocalId")]
struct ItemLocalIdProxy {
    #[serde(getter = "item_local_id_as_u32")]
    private: u32,
}

impl From<ItemLocalIdProxy> for hir::ItemLocalId {
    fn from(proxy: ItemLocalIdProxy) -> hir::ItemLocalId {
        hir::ItemLocalId::from_u32(proxy.private)
    }
}

fn def_index_as_u32(i: &def_id::DefIndex) -> u32 {
    i.as_u32()
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "def_id::DefIndex")]
struct DefIndexProxy {
    #[serde(getter = "def_index_as_u32")]
    private: u32,
}

impl From<DefIndexProxy> for def_id::DefIndex {
    fn from(proxy: DefIndexProxy) -> def_id::DefIndex {
        def_id::DefIndex::from_u32(proxy.private)
    }
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "def_id::LocalDefId")]
struct LocalDefIdProxy {
    #[serde(with = "DefIndexProxy")]
    local_def_index: def_id::DefIndex,
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "hir::hir_id::OwnerId")]
struct OwnerIdProxy {
    #[serde(with = "LocalDefIdProxy")]
    def_id: def_id::LocalDefId,
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "hir::HirId")]
struct HirIdProxy {
    #[serde(with = "OwnerIdProxy")]
    owner: hir::OwnerId,
    #[serde(with = "ItemLocalIdProxy")]
    local_id: hir::ItemLocalId,
}

#[derive(Deserialize, Serialize)]
#[serde(remote = "hir::BodyId")]
pub struct BodyIdProxy {
    #[serde(with = "HirIdProxy")]
    hir_id: hir::HirId,
}

/// This exists because of serde's restrictions on how you derive serializers.
/// [`BodyIdProxy`] can be used to serialize a [`BodyId`](hir::BodyId) but if
/// the [`BodyId`](hir::BodyId) is used as e.g. a key in a map or in a vector it
/// does not dispatch to the remote impl on [`BodyIdProxy`]. Implementing the
/// serializers for the map or vector by hand is annoying so instead you can map
/// over the datastructure, wrap each [`BodyId`](hir::BodyId) in this proxy type
/// and then dispatch to the `serialize` impl for the reconstructed data
/// structure.
#[derive(Serialize, Deserialize)]
pub struct BodyIdProxy2(#[serde(with = "BodyIdProxy")] pub hir::BodyId);
