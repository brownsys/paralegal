//! JSON serializers, most used for debugging output in [`crate::dbg`].
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

use crate::{
    ir::{
        format_global_location, CallDeps, CallOnlyFlow, GlobalLocation, GlobalLocationS,
        IsGlobalLocation,
    },
    mir,
    rust::TyCtxt,
    serde::{Serialize, Serializer},
    utils::{extract_places, read_places_with_provenance, DfppBodyExt},
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
    use crate::mir;
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
    /// Create a serializable version of a `mir::Body` by stringifying
    /// everything.
    ///
    /// Includes, as the set of places for each statements the read places with
    /// provenance as calculated by [`read_places_with_provenance`].
    pub fn from_body_with_normalize<'tcx>(body: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self(
            iter_stmts(body)
                .map(|(loc, stmt)| {
                    (
                        loc,
                        stmt.either(|s| format!("{:?}", s.kind), |t| format!("{:?}", t.kind)),
                        read_places_with_provenance(loc, &body.stmt_at_better_err(loc), tcx)
                            .map(|p| Symbol::intern(&format!("{p:?}")))
                            .collect(),
                    )
                })
                .collect::<Vec<_>>(),
        )
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

use crate::rust::hir::{self, def_id};

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
#[serde(remote = "hir::HirId")]
struct HirIdProxy {
    #[serde(with = "LocalDefIdProxy")]
    owner: def_id::LocalDefId,
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

/// A serializable non-interned version of [`GlobalLocation`].
///
/// Thanks to the [`IsGlobalLocation`] trait you can use this the same way as a
/// [`GlobalLocation`]. Though be aware that this struct is significantly larger
/// in memory as it contains a singly-linked list of call chains that is not
/// interned.
///
/// For information on the meaning of this struct see [`GlobalLocation`]
#[derive(Deserialize, Serialize, PartialEq, Eq, Hash)]
pub struct RawGlobalLocation(Vec<GlobalLocationS>);

impl<'g> From<&'_ GlobalLocation<'g>> for RawGlobalLocation {
    fn from(other: &GlobalLocation<'g>) -> Self {
        RawGlobalLocation(other.to_owned())
    }
}

impl std::fmt::Display for RawGlobalLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        format_global_location(self, f)
    }
}

impl IsGlobalLocation for RawGlobalLocation {
    fn as_slice(&self) -> &[GlobalLocationS] {
        &self.0
    }
}

impl<'g> Serialize for GlobalLocation<'g> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        RawGlobalLocation::from(self).serialize(serializer)
    }
}
pub type SerializableCallOnlyFlow = CallOnlyFlow<RawGlobalLocation>;

pub mod serde_map_via_vec {
    //! Serialize a [`HashMap`] by converting it to a [`Vec`], lifting
    //! restrictions on the types of permissible keys.
    //!
    //! The JSON serializer for [`HashMap`] needs the keys to serialize to a
    //! JSON string object, but sometimes that is not the case. Since the
    //! [`HashMap`] struct only requires its keys be [`Eq`] and [`Hash`] other
    //! non-string values may have been used as key (such is the case in
    //! [`Bodies`](super::Bodies)). Unfortunately you can still use the
    //! [`Serialize`] trait on [`HashMap`], even if the keys do not serialize to
    //! strings. Instead a runtime error will be thrown when a non-string key is
    //! encountered.
    //!
    //! This module converts the [`HashMap`] into a [`Vec`] of tuples and
    //! (de)serializes that, which permits arbitrary types to be used for the
    //! keys.
    //!
    //! You are meant to use both [`serialize`] and [`deserialize`], because the
    //! [`Serialize`] and [`Deserialize`] instances of [`HashMap`] do not work
    //! together with these functions.

    use crate::HashMap;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    /// Serialize a [`HashMap`] by first converting to a [`Vec`] of tuples and
    /// then serializing the vector.
    ///
    /// See module level documentation for usage information.
    pub fn serialize<S: Serializer, K: Serialize, V: Serialize>(
        map: &HashMap<K, V>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        map.iter().collect::<Vec<_>>().serialize(serializer)
    }

    /// Deserialize a [`HashMap`] by first deserializing a [`Vec`] of tuples and
    /// then converting.
    ///
    /// See module level documentation for usage information.
    pub fn deserialize<
        'de,
        D: Deserializer<'de>,
        K: Deserialize<'de> + std::cmp::Eq + std::hash::Hash,
        V: Deserialize<'de>,
    >(
        deserializer: D,
    ) -> Result<HashMap<K, V>, D::Error> {
        Ok(Vec::deserialize(deserializer)?.into_iter().collect())
    }
}

impl SerializableCallOnlyFlow {
    pub fn all_locations_iter(&self) -> impl Iterator<Item = &RawGlobalLocation> {
        self.location_dependencies.iter().flat_map(|(from, deps)| {
            std::iter::once(from).chain(
                std::iter::once(&deps.ctrl_deps)
                    .chain(deps.input_deps.iter())
                    .flat_map(|d| d.iter()),
            )
        })
    }
}

impl CallOnlyFlow<GlobalLocation<'_>> {
    pub fn make_serializable(&self) -> SerializableCallOnlyFlow {
        CallOnlyFlow {
            location_dependencies: self
                .location_dependencies
                .iter()
                .map(|(g, v)| {
                    (
                        g.into(),
                        CallDeps {
                            ctrl_deps: v.ctrl_deps.iter().map(|l| l.into()).collect(),
                            input_deps: v
                                .input_deps
                                .iter()
                                .map(|hs| hs.iter().map(|d| d.into()).collect())
                                .collect(),
                        },
                    )
                })
                .collect(),
            return_dependencies: self.return_dependencies.iter().map(|l| l.into()).collect(),
        }
    }
}
/// A serializable version of [`mir::Body`]s, mapped to their [`hir::BodyId`] so
/// that you can resolve the body belonging to a global location (see
/// [`IsGlobalLocation::function`]).
pub struct Bodies(pub HashMap<hir::BodyId, (Symbol, BodyProxy)>);

impl Serialize for Bodies {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0
            .iter()
            .map(|(bid, (name, b))| (BodyIdProxy2(*bid), (SymbolProxy(*name), b)))
            .collect::<Vec<_>>()
            .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Bodies {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Vec::deserialize(deserializer).map(|v| {
            Bodies(
                v.into_iter()
                    .map(|(BodyIdProxy2(bid), (SymbolProxy(s), v))| (bid, (s, v)))
                    .collect(),
            )
        })
    }
}
