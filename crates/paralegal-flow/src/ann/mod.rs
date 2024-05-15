use flowistry_pdg_construction::graph::InternedString;
use rustc_macros::{Decodable, Encodable};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use serde::{Deserialize, Serialize};

use paralegal_spdg::{rustc_proxies, tiny_bitset_pretty, Identifier, TinyBitSet, TypeId};

pub mod db;
pub mod parse;

/// Types of annotations we support.
///
/// Usually you'd expect one of those annotation types in any given situation.
/// For convenience the match methods [`Self::as_marker`], [`Self::as_otype`]
/// and [`Self::as_exception`] are provided. These are particularly useful in
/// conjunction with e.g. [`Iterator::filter_map`]
#[derive(
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Debug,
    Clone,
    Deserialize,
    Serialize,
    strum::EnumIs,
    Encodable,
    Decodable,
)]
pub enum Annotation {
    Marker(MarkerAnnotation),
    OType(OType),
    Exception(ExceptionAnnotation),
}
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy, Deserialize, Serialize)]
pub struct OType {
    #[serde(with = "rustc_proxies::DefId")]
    pub def_id: TypeId,
}

impl<E: Encoder> Encodable<E> for OType {
    fn encode(&self, s: &mut E) {
        rustc_middle::ty::tls::with(|tcx| tcx.def_path_hash(self.def_id)).encode(s)
    }
}

impl<D: Decoder> Decodable<D> for OType {
    fn decode(d: &mut D) -> Self {
        Self {
            def_id: rustc_middle::ty::tls::with(|tcx| {
                tcx.def_path_hash_to_def_id(Decodable::decode(d), &mut || {
                    panic!("Could not resolve def path")
                })
            }),
        }
    }
}

impl Annotation {
    /// If this is an [`Annotation::Marker`], returns the underlying [`MarkerAnnotation`].
    pub fn as_marker(&self) -> Option<&MarkerAnnotation> {
        match self {
            Annotation::Marker(l) => Some(l),
            _ => None,
        }
    }

    /// If this is an [`Annotation::OType`], returns the underlying [`TypeId`].
    pub fn as_otype(&self) -> Option<TypeId> {
        match self {
            Annotation::OType(t) => Some(t.def_id),
            _ => None,
        }
    }

    /// If this is an [`Annotation::Exception`], returns the underlying [`ExceptionAnnotation`].
    pub fn as_exception(&self) -> Option<&ExceptionAnnotation> {
        match self {
            Annotation::Exception(e) => Some(e),
            _ => None,
        }
    }
}

pub type VerificationHash = u128;

#[derive(
    PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Serialize, Deserialize, Encodable, Decodable,
)]
pub struct ExceptionAnnotation {
    /// The value of the verification hash we found in the annotation. Is `None`
    /// if there was no verification hash in the annotation.
    pub verification_hash: Option<VerificationHash>,
}

/// A marker annotation and its refinements.
#[derive(
    PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Serialize, Deserialize, Encodable, Decodable,
)]
pub struct MarkerAnnotation {
    /// The (unchanged) name of the marker as provided by the user
    pub marker: InternedString,
    #[serde(flatten)]
    pub refinement: MarkerRefinement,
}

fn const_false() -> bool {
    false
}

/// Refinements in the marker targeting. The default (no refinement provided) is
/// `on_argument == vec![]` and `on_return == false`, which is also what is
/// returned from [`Self::empty`].
#[derive(
    PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Deserialize, Serialize, Encodable, Decodable,
)]
pub struct MarkerRefinement {
    #[serde(default, with = "tiny_bitset_pretty")]
    on_argument: TinyBitSet,
    #[serde(default = "const_false")]
    on_return: bool,
}

/// Disaggregated version of [`MarkerRefinement`]. Can be added to an existing
/// refinement [`MarkerRefinement::merge_kind`].
#[derive(Clone, Deserialize, Serialize)]
pub enum MarkerRefinementKind {
    Argument(#[serde(with = "tiny_bitset_pretty")] TinyBitSet),
    Return,
}

impl MarkerRefinement {
    /// The default, empty aggregate refinement `Self { on_argument: vec![],
    /// on_return: false }`
    pub fn empty() -> Self {
        Self {
            on_argument: Default::default(),
            on_return: false,
        }
    }

    /// Merge the aggregate refinement with another discovered refinement and
    /// check that they do not overwrite each other.
    pub fn merge_kind(mut self, k: MarkerRefinementKind) -> Result<Self, String> {
        match k {
            MarkerRefinementKind::Argument(a) => {
                if self.on_argument.is_empty() {
                    self.on_argument = a;
                    Ok(self)
                } else {
                    Err(format!(
                        "Double argument annotation {:?} and {a:?}",
                        self.on_argument
                    ))
                }
            }
            MarkerRefinementKind::Return => {
                if !self.on_return {
                    self.on_return = true;
                    Ok(self)
                } else {
                    Err("Double on-return annotation".to_string())
                }
            }
        }
    }

    /// Get the refinements on arguments
    pub fn on_argument(&self) -> TinyBitSet {
        self.on_argument
    }

    /// Is this refinement targeting the return value?
    pub fn on_return(&self) -> bool {
        self.on_return
    }

    /// True if this refinement is empty, i.e. the annotation is targeting the
    /// item itself.
    pub fn on_self(&self) -> bool {
        self.on_argument.is_empty() && !self.on_return
    }
}
