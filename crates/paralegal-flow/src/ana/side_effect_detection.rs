

const ALLOWED_INTRINSICS: &str = [
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

const ALLOWED_FUNCTIONS: &[&str] = [
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
