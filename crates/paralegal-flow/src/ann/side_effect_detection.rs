use std::collections::HashSet;

use flowistry_pdg_construction::utils::is_virtual;
use paralegal_spdg::Identifier;

use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty};

use either::Either;

use crate::{ann::db::AutoMarkers, MarkerCtx};

const ALLOWED_INTRINSICS: &[&str] = &[
    // Prefetching.
    "prefetch_read_data",
    "prefetch_write_data",
    "prefetch_read_instruction",
    "prefetch_write_instruction",
    // Optimizer.
    "likely",
    "unlikely",
    "unreachable",
    "assume",
    "black_box",
    // Breakpoint.
    "breakpoint",
    // size_of and others.
    "size_of",
    "min_align_of",
    "pref_align_of",
    "size_of_val",
    "min_align_of_val",
    // Assertions.
    "assert_inhabited",
    "assert_zero_valid",
    "assert_mem_uninitialized_valid",
    // Needs drop.
    "needs_drop",
    // Offsets.
    "arith_offset",
    "offset",
    // Ptr mask.
    "ptr_mask",
    // Number operations.
    "sqrtf32",
    "sqrtf64",
    "powif32",
    "powif64",
    "sinf32",
    "sinf64",
    "cosf32",
    "cosf64",
    "powf32",
    "powf64",
    "expf32",
    "expf64",
    "exp2f32",
    "exp2f64",
    "logf32",
    "logf64",
    "log10f32",
    "log10f64",
    "log2f32",
    "log2f64",
    "fmaf32",
    "fmaf64",
    "fabsf32",
    "fabsf64",
    "minnumf32",
    "minnumf64",
    "maxnumf32",
    "maxnumf64",
    "copysignf32",
    "copysignf64",
    "floorf32",
    "floorf64",
    "ceilf32",
    "ceilf64",
    "truncf32",
    "truncf64",
    "rintf32",
    "rintf64",
    "nearbyintf32",
    "nearbyintf64",
    "roundf32",
    "roundf64",
    "roundevenf32",
    "roundevenf64",
    "fadd_fast",
    "fsub_fast",
    "fmul_fast",
    "fdiv_fast",
    "frem_fast",
    "float_to_int_unchecked",
    // Bit operations
    "ctpop",
    "ctlz",
    "ctlz_nonzero",
    "cttz",
    "cttz_nonzero",
    "bswap",
    "bitreverse",
    // Arithmetic operations with overflow.
    "add_with_overflow",
    "sub_with_overflow",
    "mul_with_overflow",
    // Rotates.
    "rotate_left",
    "rotate_right",
    // Wrapping arithmetic operations.
    "wrapping_add",
    "wrapping_sub",
    "wrapping_mul",
    // Saturating arithmetic operations.
    "saturating_add",
    "saturating_sub",
    // Read arbitrary memory.
    "read_via_copy",
    // Discriminants.
    "discriminant_value",
    // Variants.
    "variant_count",
    // const* business.
    "ptr_offset_from",
    "ptr_offset_from_unsigned",
    "ptr_guaranteed_cmp",
    // Constant evaluation.
    "const_allocate",
    "const_deallocate",
    "const_eval_select",
    // Raw equality comparison.
    "raw_eq",
    "compare_bytes",
    // Vtable.
    "vtable_size",
    "vtable_align",
    // Unchecked arithmetic operations.
    "exact_div",
    "unchecked_add",
    "unchecked_div",
    "unchecked_mul",
    "unchecked_rem",
    "unchecked_shl",
    "unchecked_shr",
    "unchecked_sub",
    // Dynamic typing.
    "type_id",
    "type_name",
    // Transmute is allowlisted as an intrinsic, but is checked for separately.
    // Justus: I don't know why Artem was checking for this separately. For now
    // I disallow this, though I still special case it with it's own effect
    // type.
    // "transmute",
];

pub(super) fn allowed_intrinsics() -> FxHashSet<rustc_span::Symbol> {
    ALLOWED_INTRINSICS
        .iter()
        .copied()
        .map(rustc_span::Symbol::intern)
        .collect()
}

pub fn is_allowed_as_clone_unit_instance<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> bool {
    let fn_id = instance.def_id();
    let generics = instance.args;

    tcx.lang_items().clone_fn().is_some_and(|c| c == fn_id)
        && matches!(generics.as_slice(), [ty] if ty.as_type().is_some_and(ty::Ty::is_unit))
}

pub fn analyze_body<'tcx>(
    body: &mir::Body<'tcx>,
    auto_markers: &AutoMarkers,
    tcx: ty::TyCtxt<'tcx>,
) -> FxHashSet<Identifier> {
    use mir::visit::Visitor;
    let mut analyzer = BodyAnalyzer::new(body, auto_markers, tcx);
    analyzer.visit_body(body);
    analyzer.found_markers
}

pub fn analyze_statement<'tcx>(
    body: &mir::Body<'tcx>,
    location: mir::Location, // we take location here so we can guarantee that the statement is within the body
    auto_markers: &AutoMarkers,
    tcx: ty::TyCtxt<'tcx>,
) -> FxHashSet<Identifier> {
    use mir::visit::Visitor;

    let mut analyzer = BodyAnalyzer::new(body, auto_markers, tcx);
    match body.stmt_at(location) {
        Either::Left(statement) => {
            analyzer.visit_statement(statement, location);
            trace!(
                "Checking statement {:?}, found {:?}",
                statement.kind,
                analyzer.found_markers
            );
        }
        Either::Right(terminator) => {
            analyzer.visit_terminator(terminator, location);
        }
    }
    analyzer.found_markers
}

struct BodyAnalyzer<'tcx, 'b> {
    body: &'b mir::Body<'tcx>,
    found_markers: FxHashSet<Identifier>,
    auto_markers: &'b AutoMarkers,
    tcx: ty::TyCtxt<'tcx>,
}

impl<'tcx, 'b> BodyAnalyzer<'tcx, 'b> {
    fn new(
        body: &'b mir::Body<'tcx>,
        auto_markers: &'b AutoMarkers,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Self {
        Self {
            body,
            found_markers: HashSet::default(),
            auto_markers,
            tcx,
        }
    }
}

impl<'tcx> mir::visit::Visitor<'tcx> for BodyAnalyzer<'tcx, '_> {
    fn visit_projection_elem(
        &mut self,
        place_ref: mir::PlaceRef<'tcx>,
        projection_elem: mir::PlaceElem<'tcx>,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        if matches!(projection_elem, mir::ProjectionElem::Deref) {
            let ty = place_ref.ty(self.body, self.tcx).ty;

            if ty.is_mutable_ptr() && ty.is_unsafe_ptr() {
                self.found_markers
                    .insert(self.auto_markers.side_effect_raw_ptr);
            }
        }
        self.super_projection_elem(place_ref, projection_elem, context, location);
    }

    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: mir::Location) {
        if let mir::Rvalue::Cast(mir::CastKind::Transmute, _, to) = rvalue {
            trace!("Found transmute in {rvalue:?}");
            if contains_mut_ref(*to, self.tcx) {
                self.found_markers
                    .insert(self.auto_markers.side_effect_transmute);
            }
        }
        self.super_rvalue(rvalue, location);
    }
}

fn contains_mut_ref<'tcx>(ty: ty::Ty<'tcx>, tcx: ty::TyCtxt<'tcx>) -> bool {
    use ty::{TypeSuperVisitable, TypeVisitable};
    struct ContainsMutRefVisitor<'tcx> {
        tcx: ty::TyCtxt<'tcx>,
        has_mut_ref: bool,
    }

    impl<'tcx> ty::TypeVisitor<ty::TyCtxt<'tcx>> for ContainsMutRefVisitor<'tcx> {
        fn visit_ty(&mut self, t: ty::Ty<'tcx>) {
            if let ty::TyKind::Adt(adt_def, substs) = t.kind() {
                for field in adt_def.all_fields() {
                    field.ty(self.tcx, substs).visit_with(self);
                }
            }

            if let Some(mir::Mutability::Mut) = t.ref_mutability() {
                trace!("Found mut ref in {t:?}");
                self.has_mut_ref = true;
            }
            t.super_visit_with(self)
        }
    }

    let mut visitor = ContainsMutRefVisitor {
        tcx,
        has_mut_ref: false,
    };
    ty.visit_with(&mut visitor);
    visitor.has_mut_ref
}

impl MarkerCtx<'_> {
    pub fn marker_if_unloadable(&self, def_id: DefId) -> Option<&Identifier> {
        let auto_markers = self.auto_markers();
        let tcx = self.tcx();
        if is_virtual(tcx, def_id) {
            trace!("  Is virtual");
            Some(&auto_markers.side_effect_unknown_virtual)
        } else if tcx.is_foreign_item(def_id) {
            trace!("  Is foreign");
            Some(&auto_markers.side_effect_foreign)
        } else if let Some(idef) = tcx.intrinsic(def_id) {
            if idef.name.as_str() == "transmute" {
                Some(&auto_markers.side_effect_transmute)
            } else if self.is_allowed_intrinsic(idef.name) {
                None
            } else {
                Some(&auto_markers.side_effect_intrinsic)
            }
        } else {
            None
        }
    }
}
