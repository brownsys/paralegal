use std::{collections::HashSet, sync::OnceLock};

use paralegal_spdg::Identifier;

use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty};

use either::Either;

use crate::{ann::db::AutoMarkers, utils::resolve, Pctx};

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
    "transmute",
];

const ALLOWED_FUNCTIONS: &[&str] = &[
    // Panicking infrastructure.
    "core::panicking::assert_failed",
    "core::panicking::const_panic_fmt",
    "core::panicking::panic",
    "core::panicking::panic_display",
    "core::panicking::panic_fmt",
    "core::panicking::panic_nounwind",
    "core::panicking::panic_nounwind_fmt",
    "core::panicking::panic_str",
    "core::panicking::unreachable_display",
    // Alloc infrastructure.
    "alloc::alloc::alloc",
    "alloc::alloc::alloc_zeroed",
    "alloc::alloc::dealloc",
    "alloc::alloc::realloc",
    // Impls of global allocator.
    // "alloc::alloc::\{impl#0\}",
    // "alloc::alloc::\{impl#1\}",
    // Alloc error handler.
    "alloc::alloc::__rust_alloc_error_handler",
    // Format chrono.
    "chrono::naive::datetime::format",
    "alloc::string::to_string",
    "core::fmt::new",
    // Format strings.
    "alloc::fmt::format",
    // "core::fmt::rt::\{impl#1\}::new",

    // Rust 1.70 calls to memcmp to compare slices.
    // This is removed in further versions.
    // "core::slice::cmp::\{extern#0\}::memcmp",

    // Architecture-dependent intrinsics.
    "core::core_arch",
    // Pointer-address conversion primitives.
    "core::ptr::invalid",
    "core::ptr::invalid_mut",
    "core::ptr::const_ptr::addr",
    "core::ptr::mut_ptr::addr",
    "core::ptr::alignment::new_unchecked",
];

const TRUSTED_MODULES: &[&str] = &[
    "alloc::vec",
    "alloc::slice",
    "core::slice",
    "alloc::string",
    "std::collections::hash::map",
    "alloc::collections::btree",
];

static RESOLVED_ALLOWED_ITEMS: OnceLock<FxHashSet<DefId>> = OnceLock::new();

fn flatten_child_items<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    modules: impl IntoIterator<Item = DefId>,
) -> FxHashSet<DefId> {
    use rustc_hir::def::DefKind;
    let mut queue: Vec<_> = modules.into_iter().collect();
    let mut seen = FxHashSet::default();
    seen.extend(queue.iter().cloned());
    let mut result = FxHashSet::default();

    while let Some(module) = queue.pop() {
        for c in tcx.module_children(module) {
            let Some(id) = c.res.opt_def_id() else {
                continue;
            };

            match tcx.def_kind(id) {
                DefKind::Mod if !seen.contains(&id) => {
                    seen.insert(id);
                    queue.push(id);
                }
                DefKind::Fn | DefKind::AssocFn | DefKind::Closure => {
                    result.insert(id);
                }
                _ => {}
            }
        }
    }

    result
}

fn allowed_precheck(def_id: DefId, tcx: ty::TyCtxt<'_>) -> bool {
    let resolve = |name| match resolve::resolve_string_to_def_id(tcx, name) {
        Ok(resolve::Res::Def(_, did)) => Some(did),
        Ok(other) => {
            tcx.dcx().err(format!(
                "Expected to resolve to a definition, got {:?}",
                other
            ));
            None
        }
        Err(e) => {
            // We allow this case so that we can add functions from external crates to the allowlist
            if !matches!(e, resolve::ResolutionError::CouldNotResolveCrate(_)) {
                tcx.dcx().err(format!("Error resolving {name}: {:?}", e));
            }
            None
        }
    };
    RESOLVED_ALLOWED_ITEMS
        .get_or_init(|| {
            let mut set =
                flatten_child_items(tcx, TRUSTED_MODULES.iter().filter_map(|name| resolve(name)));
            set.extend(ALLOWED_FUNCTIONS.iter().filter_map(|name| resolve(name)));
            set
        })
        .contains(&def_id)
}

pub fn analyze_body<'tcx, 'b>(
    def_id: DefId,
    body: &'b mir::Body<'tcx>,
    auto_markers: &AutoMarkers,
    tcx: ty::TyCtxt<'tcx>,
) -> FxHashSet<Identifier> {
    if allowed_precheck(def_id, tcx) {
        return FxHashSet::default();
    }

    use mir::visit::Visitor;
    let mut analyzer = BodyAnalyzer::new(body, auto_markers, tcx);
    analyzer.visit_body(body);
    analyzer.found_markers
}

pub fn analyze_statement<'tcx, 'b>(
    def_id: DefId,
    body: &'b mir::Body<'tcx>,
    location: mir::Location, // we take location here so we can guarantee that the statement is within the body
    auto_markers: &AutoMarkers,
    tcx: ty::TyCtxt<'tcx>,
) -> FxHashSet<Identifier> {
    if allowed_precheck(def_id, tcx) {
        return FxHashSet::default();
    }

    use mir::visit::Visitor;

    let mut analyzer = BodyAnalyzer::new(body, auto_markers, tcx);
    match body.stmt_at(location) {
        Either::Left(statement) => {
            analyzer.visit_statement(statement, location);
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

impl<'tcx, 'b> mir::visit::Visitor<'tcx> for BodyAnalyzer<'tcx, 'b> {
    fn visit_projection(
        &mut self,
        place_ref: mir::PlaceRef<'tcx>,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        if matches!(
            (place_ref.projection.last(), context),
            (
                Some(mir::ProjectionElem::Deref),
                mir::visit::PlaceContext::MutatingUse(_)
            )
        ) {
            let ty = place_ref.ty(self.body, self.tcx).ty;

            if ty.is_mutable_ptr() && ty.is_unsafe_ptr() {
                self.found_markers
                    .insert(self.auto_markers.side_effect_raw_ptr);
            }
        }
        self.super_projection(place_ref, context, location);
    }

    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: mir::Location) {
        if let mir::Rvalue::Cast(mir::CastKind::Transmute, _, to) = rvalue {
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
