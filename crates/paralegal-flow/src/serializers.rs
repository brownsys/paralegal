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
use paralegal_spdg::{rustc_portable::DefId, Identifier};
use serde::Deserialize;

use crate::{
    mir,
    rust::TyCtxt,
    serde::{Serialize, Serializer},
    utils::{extract_places, read_places_with_provenance, DfppBodyExt},
    Either, HashMap, HashSet,
};

#[derive(Debug, Serialize, Deserialize)]
pub struct InstructionProxy {
    #[serde(with = "paralegal_spdg::rustc_proxies::Location")]
    pub location: mir::Location,
    pub contents: String,
    pub places: HashSet<Identifier>,
}

/// A serializable version of a `mir::Body`.
///
/// Be aware that this transports less information than the actual `mir::Body`.
/// It records for each [`mir::Location`] a string representation of the
/// statement or terminator at that location and a set of [`mir::Place`]s that
/// are mentioned in the statement/terminator, also represented as strings
/// (though using the efficient, interned [`Identifier`]s).
///
/// Construct one with [`Self::from_body_with_normalize`].
#[derive(Debug, Serialize, Deserialize)]
pub struct BodyProxy(pub Vec<InstructionProxy>);

fn iter_stmts<'a, 'tcx>(
    b: &'a mir::Body<'tcx>,
) -> impl Iterator<
    Item = (
        mir::Location,
        Either<&'a mir::Statement<'tcx>, &'a mir::Terminator<'tcx>>,
    ),
> {
    b.basic_blocks.iter_enumerated().flat_map(|(block, bbdat)| {
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
                .map(|(location, stmt)| InstructionProxy {
                    location,
                    contents: stmt.either(|s| format!("{:?}", s.kind), |t| format!("{:?}", t.kind)),
                    places: extract_places(location, body, false)
                        .into_iter()
                        .map(|p| Identifier::new_intern(&format!("{p:?}")))
                        .collect(),
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
                .map(|(location, stmt)| InstructionProxy {
                    location,
                    contents: stmt.either(|s| format!("{:?}", s.kind), |t| format!("{:?}", t.kind)),
                    places: read_places_with_provenance(
                        location,
                        &body.stmt_at_better_err(location),
                        tcx,
                    )
                    .map(|p| Identifier::new_intern(&format!("{p:?}")))
                    .collect(),
                })
                .collect::<Vec<_>>(),
        )
    }
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
pub struct BodyIdProxy2(#[serde(with = "paralegal_spdg::rustc_proxies::DefId")] pub DefId);

/// A serializable version of [`mir::Body`]s, mapped to their [`hir::BodyId`] so
/// that you can resolve the body belonging to a global location (see
/// [`IsGlobalLocation::function`]).
pub struct Bodies(pub HashMap<DefId, (Identifier, BodyProxy)>);

impl Serialize for Bodies {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0
            .iter()
            .map(|(bid, (name, b))| (BodyIdProxy2(*bid), *name, b))
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
                    .map(|(BodyIdProxy2(bid), s, v)| (bid, (s, v)))
                    .collect(),
            )
        })
    }
}
