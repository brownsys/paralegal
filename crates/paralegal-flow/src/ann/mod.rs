use std::fmt::{Display, Write};

use either::Either;
use flowistry_pdg_construction::{body_cache::intermediate_out_dir, encoder::ParalegalEncoder};
use rustc_ast::Attribute;

use rustc_hir::{
    def_id::DefIndex,
    intravisit::{self, nested_filter::NestedFilter},
};
use rustc_macros::{Decodable, Encodable};
use rustc_middle::{hir::map::Map, ty::TyCtxt};
use rustc_serialize::Encodable;
use serde::{Deserialize, Serialize};

use paralegal_spdg::{
    rustc_proxies, tiny_bitset_pretty, utils::write_sep, Identifier, TinyBitSet, TypeId,
};

pub mod db;
pub mod parse;

use parse::*;

use crate::{discover::AttrMatchT, sym_vec, utils::MetaItemMatch};

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
    pub marker: Identifier,
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

impl Display for MarkerRefinement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.on_argument.is_empty() {
            f.write_str("argument = [")?;
            write_sep(
                f,
                ", ",
                self.on_argument.into_iter_set_in_domain(),
                |elem, f| elem.fmt(f),
            )?;
            f.write_char(']')?;
            if self.on_return {
                f.write_str(" + ")?;
            }
        }
        if self.on_return {
            f.write_str("return")?;
        }
        Ok(())
    }
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

/// These are pseudo-constants that are used to match annotations. In theory
/// they never change but they use [`Symbol`] inside, which is only valid so
/// long as the rustc `SESSION_GLOBALS` are live so we need to calculate them
/// afresh in `new`.
struct Markers {
    /// This will match the annotation `#[paralegal_flow::label(...)]` when using
    /// [`MetaItemMatch::match_extract`](crate::utils::MetaItemMatch::match_extract)
    label_marker: AttrMatchT,
    /// This will match the annotation `#[paralegal_flow::marker(...)]` when using
    /// [`MetaItemMatch::match_extract`](crate::utils::MetaItemMatch::match_extract)
    marker_marker: AttrMatchT,
    /// This will match the annotation `#[paralegal_flow::output_types(...)]` when using
    /// [`MetaItemMatch::match_extract`](crate::utils::MetaItemMatch::match_extract)
    otype_marker: AttrMatchT,
    /// This will match the annotation `#[paralegal_flow::exception(...)]` when using
    /// [`MetaItemMatch::match_extract`](crate::utils::MetaItemMatch::match_extract)
    exception_marker: AttrMatchT,
}

impl Default for Markers {
    fn default() -> Self {
        Markers {
            label_marker: sym_vec!["paralegal_flow", "label"],
            marker_marker: sym_vec!["paralegal_flow", "marker"],
            otype_marker: sym_vec!["paralegal_flow", "output_types"],
            exception_marker: sym_vec!["paralegal_flow", "exception"],
        }
    }
}

type MarkerMeta = Vec<(DefIndex, Vec<Annotation>)>;

struct DumpingVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    annotations: MarkerMeta,
    markers: Markers,
    symbols: Symbols,
}

impl<'hir> NestedFilter<'hir> for VisitFilter {
    type Map = Map<'hir>;

    const INTER: bool = true;
    const INTRA: bool = true;
}

struct VisitFilter;

impl<'tcx> intravisit::Visitor<'tcx> for DumpingVisitor<'tcx> {
    type NestedFilter = VisitFilter;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_id(&mut self, hir_id: rustc_hir::HirId) {
        let Some(owner) = hir_id.as_owner() else {
            return;
        };
        let v: Vec<_> = self
            .tcx
            .hir()
            .attrs(hir_id)
            .iter()
            .flat_map(|ann| self.try_parse_annotation(ann).unwrap())
            .collect();
        if !v.is_empty() {
            self.annotations.push((owner.def_id.local_def_index, v));
        }
    }
}

impl<'tcx> DumpingVisitor<'tcx> {
    fn try_parse_annotation(
        &self,
        a: &Attribute,
    ) -> Result<impl Iterator<Item = Annotation>, String> {
        let consts = &self.markers;
        let tcx = self.tcx;
        let one = |a| Either::Left(Some(a));
        let ann = if let Some(i) = a.match_get_ref(&consts.marker_marker) {
            one(Annotation::Marker(ann_match_fn(&self.symbols, i)?))
        } else if let Some(i) = a.match_get_ref(&consts.label_marker) {
            warn!("The `paralegal_flow::label` annotation is deprecated, use `paralegal_flow::marker` instead");
            one(Annotation::Marker(ann_match_fn(&self.symbols, i)?))
        } else if let Some(i) = a.match_get_ref(&consts.otype_marker) {
            Either::Right(otype_ann_match(i, tcx)?.into_iter().map(Annotation::OType))
        } else if let Some(i) = a.match_get_ref(&consts.exception_marker) {
            one(Annotation::Exception(match_exception(&self.symbols, i)?))
        } else {
            Either::Left(None)
        };
        Ok(ann.into_iter())
    }
}

const MARKER_META_EXT: &str = "pmeta";

/// A visit over the HIR that collects all the marker annotations we can find
/// and dumps them out
pub fn dump_markers(tcx: TyCtxt) {
    let mut vis = DumpingVisitor {
        tcx,
        annotations: Default::default(),
        markers: Markers::default(),
        symbols: Default::default(),
    };
    tcx.hir().visit_all_item_likes_in_crate(&mut vis);
    let mut encoder = ParalegalEncoder::new(intermediate_out_dir(tcx, MARKER_META_EXT), tcx);
    vis.annotations.encode(&mut encoder);
    encoder.finish();
}
