//! A sparse dependency tensor similar to flowistry's Θ. 
//! 
//! Additionally supports optional translation between [`Place`]s.

use super::global_location::*;
use crate::{rust::*, HashMap, HashSet};

use mir::Place;

pub type PlaceTranslationTable<'tcx> = HashMap<Place<'tcx>, Place<'tcx>>;

/// A flowistry-like dependency matrix at a specific location. Describes for
/// each place the most recent global locations (these could be locations in a
/// callee) that influenced the values at this place.
pub type GlobalDepMatrix<'tcx, 'g> = HashMap<Place<'tcx>, HashSet<GlobalLocation<'g>>>;

/// A [`GlobalDepMatrix`] that may also translate between places.
///
/// A [`Place`] value is always relative to (and only unique in) a
/// [`mir::Body`]. As such when we inline one body into another both may define
/// the same place (e.g. the return place `_0`). This means we need a way to
/// translate from places of the caller to places of the callee and vice-versa
/// when we perform cross-function dependency analysis. At special boundary
/// locations (the call sites) we therefore have dependency matrices that
/// translate between places.
///
/// There are two types of locations in a [`super::GlobalFlowGraph`] that use
/// translation (e.g. where [`is_translated`](Self::is_translated) returns
/// `true`). As an example consider
///
/// ```
/// fn bar(argument: i32) -> i32 { argument }
///
/// fn foo() {
///     let x = 1;
///     let y = bar(x);
/// }
/// ```
///
/// 1. **Caller call sites**: Location of the call site for `bar` (probably
///    `bb0[1]`) translates places from inside `bar` to places in `foo`. In this
///    case the return value `argument` (more precisely the mir place `_0` which
///    is assigned to `argument`).
///    
///    The translation tables for these locations are created with
///    [`FunctionInliner::create_callee_to_caller_translation_table`](crate::ana::FunctionInliner::create_callee_to_caller_translation_table).
/// 2. **Callee argument locations**: The special locations used by flowistry to
///    describe arguments translate places from the caller to the callee. In
///    this case the location for `argument` (probably `bb1[1]@bb0[1]`, notice
///    this is a relative location) translates the input `x` (probably place
///    `_1`) to the argument places `argument` (also probably `_1` in this
///    case).
///    
///    Translation tables for these locations are created with
///    [`FunctionInliner::create_caller_to_callee_translation_table`](crate::ana::FunctionInliner::create_caller_to_callee_translation_table).
///
/// Both of the creation methods for translation tables use
/// [`translate_child_to_parent`](crate::ana::translate_child_to_parent) under
/// the hood.
///
/// All other locations in the [`GlobalFlowGraph`](super::GlobalFlowGraph) are
/// not translated, i.e. [`resolve(p)`](Self::resolve) is the same as
/// `self.matrix.get(p)`.
///
/// The visualization for the [`GlobalFlowGraph`](super::GlobalFlowGraph) via
/// [`dbg::PrintableGranularFlow`](crate::dbg::PrintableGranularFlow) shows the
/// translation tables for locations that use translation as well for debugging
/// purposes.
///
/// To construct a matrix use [`translated`](Self::translated) or
/// [`untranslated`](Self::untranslated).
#[derive(Clone)]
pub struct TranslatedDepMatrix<'tcx, 'g> {
    /// The flowistry style dependency matrix
    matrix: GlobalDepMatrix<'tcx, 'g>,
    /// An optional mapping between places
    translator: Option<PlaceTranslationTable<'tcx>>,
}

impl<'tcx, 'g> TranslatedDepMatrix<'tcx, 'g> {
    /// Lookup this places in the translation table (if there is one).
    ///
    /// Returns none if the place was not found or if no translation table is
    /// present.
    fn resolve_place(&self, place: Place<'tcx>) -> Option<Place<'tcx>> {
        self.translator
            .as_ref()
            .and_then(|t| t.get(&place))
            .cloned()
    }

    /// Lookup the dependencies for this [`Place`].
    ///
    /// If the place has an entry in our translation table that entry is used
    /// instead of the place itself to perform the lookup. If such a translation
    /// happened the returned optional place is `Some(translation_result)` and
    /// `None` otherwise.
    pub fn resolve(
        &self,
        place: Place<'tcx>,
    ) -> (
        Option<Place<'tcx>>,
        impl Iterator<Item = GlobalLocation<'g>> + '_,
    ) {
        let resolved = self.resolve_place(place);
        (
            resolved,
            self.matrix
                .get(&resolved.unwrap_or(place))
                .into_iter()
                .flat_map(|s| s.iter())
                .cloned(),
        )
    }

    /// Lookup te dependencies for this place as a set.
    ///
    /// Only used for debug output in [`dbg`](crate::dbg). Performs translation, like
    /// [`resolve`](Self::resolve).
    pub fn resolve_set(&self, place: Place<'tcx>) -> Option<&HashSet<GlobalLocation<'g>>> {
        self.matrix.get(&self.resolve_place(place).unwrap_or(place))
    }

    /// Iterate over the keys of the dependency matrix
    pub fn keys(&self) -> impl Iterator<Item = Place<'tcx>> + '_ {
        self.matrix.keys().cloned()
    }

    /// Iterate over the values of the dependency matrix
    pub fn values(&self) -> impl Iterator<Item = &HashSet<GlobalLocation<'g>>> {
        self.matrix.values()
    }

    /// Create a dependency matrix that does not translate any places.
    pub fn untranslated(matrix: GlobalDepMatrix<'tcx, 'g>) -> Self {
        Self {
            matrix,
            translator: None,
        }
    }

    /// Create a dependency matrix that translates places using the provided
    /// translation table.
    pub fn translated(
        matrix: GlobalDepMatrix<'tcx, 'g>,
        translator: HashMap<Place<'tcx>, Place<'tcx>>,
    ) -> Self {
        Self {
            matrix,
            translator: Some(translator),
        }
    }

    /// Create a new matrix where each location has been transformed with the
    /// provided closure.
    ///
    /// See [`relativize_global_dep_matrix`].
    pub fn relativize<F: Fn(GlobalLocation<'g>) -> GlobalLocation<'g>>(
        &self,
        location_relativizer: F,
    ) -> Self {
        Self {
            translator: self.translator.clone(),
            matrix: relativize_global_dep_matrix(&self.matrix, location_relativizer),
        }
    }

    /// The raw, untranslated dependency matrix.
    ///
    /// Used only for debugging purposes in [`dbg`](crate::dbg), you should use
    /// [`resolve`](Self::resolve) instead.
    pub fn matrix_raw(&self) -> &GlobalDepMatrix<'tcx, 'g> {
        &self.matrix
    }

    /// Does this matrix perform translation, i.e. is this one of the special
    /// boundary locations.
    pub fn is_translated(&self) -> bool {
        self.translator.is_some()
    }

    /// The translation matrix used (if any).
    pub fn translator(&self) -> Option<&HashMap<Place<'tcx>, Place<'tcx>>> {
        self.translator.as_ref()
    }
}

/// Call the provided closure on every [`GlobalLocation`] in this matrix.
///
/// Usually used to relativize the location (using
/// [`gli.global_location_from_relative`](super::GLI::global_location_from_relative))
/// hence the name.
pub fn relativize_global_dep_matrix<'g, 'tcx, F: Fn(GlobalLocation<'g>) -> GlobalLocation<'g>>(
    matrix: &GlobalDepMatrix<'tcx, 'g>,
    location_relativizer: F,
) -> GlobalDepMatrix<'tcx, 'g> {
    matrix
        .iter()
        .map(|(&k, set)| (k, set.iter().cloned().map(&location_relativizer).collect()))
        .collect()
}
