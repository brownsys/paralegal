use flowistry_pdg_construction::graph::InternedString;
use rustc_macros::{Decodable, Encodable};
use serde::{Deserialize, Serialize};

use paralegal_spdg::{rustc_proxies, tiny_bitset_pretty, TinyBitSet, TypeId};

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
    OType(#[serde(with = "rustc_proxies::DefId")] TypeId),
    Exception(ExceptionAnnotation),
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
            Annotation::OType(t) => Some(*t),
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
