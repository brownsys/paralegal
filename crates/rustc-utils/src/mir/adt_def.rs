//! Utilities for [`AdtDef`].

use rustc_abi::FieldIdx;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{AdtDef, FieldDef, TyCtxt};

/// Extension trait for [`AdtDef`].
pub trait AdtDefExt<'tcx> {
    /// Returns an iterator over all the fields of the ADT that are visible
    /// from `module`.
    fn all_visible_fields(
        self,
        module: DefId,
        tcx: TyCtxt<'tcx>,
    ) -> impl Iterator<Item = &'tcx FieldDef>;

    /// Visibility-filtered iteration over a *struct's* fields, paired with
    /// each field's actual MIR `FieldIdx`.
    ///
    /// Use this whenever the iteration index will become a
    /// `ProjectionElem::Field`. The natural pattern
    /// `all_visible_fields(...).enumerate()` returns the position *within the
    /// visible subset*, NOT the source-declaration index — so any private
    /// field shifts subsequent indices and the resulting projection points
    /// at the wrong actual field.
    ///
    /// Only valid for structs (uses [`AdtDef::non_enum_variant`]). For enums,
    /// iterate per-variant via `variant.fields.iter_enumerated()`.
    fn visible_struct_fields(
        self,
        module: DefId,
        tcx: TyCtxt<'tcx>,
    ) -> impl Iterator<Item = (FieldIdx, &'tcx FieldDef)>;
}

impl<'tcx> AdtDefExt<'tcx> for AdtDef<'tcx> {
    fn all_visible_fields(
        self,
        module: DefId,
        tcx: TyCtxt<'tcx>,
    ) -> impl Iterator<Item = &'tcx FieldDef> {
        self.all_fields()
            .filter(move |field| field.vis.is_accessible_from(module, tcx))
    }

    fn visible_struct_fields(
        self,
        module: DefId,
        tcx: TyCtxt<'tcx>,
    ) -> impl Iterator<Item = (FieldIdx, &'tcx FieldDef)> {
        self.non_enum_variant()
            .fields
            .iter_enumerated()
            .filter(move |(_, field)| field.vis.is_accessible_from(module, tcx))
    }
}
