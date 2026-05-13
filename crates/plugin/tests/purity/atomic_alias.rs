//! Coverage for the resolver's handling of inherent-impl descent
//! through (1) type aliases and (2) generic-args in path segments.
//!
//! Background: every atomic type in core is `pub type AtomicX =
//! Atomic<…>` with its inherent `new` impl written under the alias
//! (`impl<T> AtomicPtr<T> { fn new ... }`). After rustc's alias-Self
//! normalization, `tcx.inherent_impls(Atomic)` contains all 12 such
//! impls. The marker resolver now supports two ways to disambiguate
//! which impl a marker should bind to:
//!
//! - **Alias-derived filter.** When a path segment is a `TyAlias`,
//!   the resolver normalizes to its target ADT and uses the alias's
//!   own substitution as a default filter. `AtomicPtr::new` therefore
//!   binds to `Atomic<*mut T>::new` (and only that).
//! - **Explicit turbofish.** A segment with generic args overrides the
//!   alias-derived filter. `Atomic::<*mut u8>::new` binds to the same
//!   `Atomic<*mut T>::new` via the supplied `*mut u8`.
//!
//! Without either signal, the resolver still picks the first
//! matching impl nondeterministically — the documented limitation #1
//! at `utils/resolve.rs:360`. The last test pins that fallback so a
//! future change closing it would surface here.

use paralegal_flow::test_utils::{
    DependencyEnvironment, DependencyEnvironmentBuilder, InlineTestBuilder,
};
use std::path::Path;
use std::sync::OnceLock;

static STDLIB_ENV: OnceLock<DependencyEnvironment> = OnceLock::new();

/// Shared env: stdlib included, `--include-std` so paralegal analyzes std
/// bodies (without it the transmute inside `AtomicPtr::new` is invisible),
/// `--side-effect-markers` to enable auto-marker insertion. No marker file
/// at the env level; tests supply per-variant marker files.
fn stdlib_env() -> &'static DependencyEnvironment {
    STDLIB_ENV.get_or_init(|| {
        DependencyEnvironmentBuilder::new()
            .with_stdlib()
            .with_extra_args(["--side-effect-markers", "--include-std"])
            .build()
    })
}

const ATOMIC_PROGRAM: &str = stringify!(
    fn main() {
        let mut x = 0u8;
        let _p = std::sync::atomic::AtomicPtr::new(&mut x as *mut u8);
    }
);

/// Baseline: without any user marker, an auto side-effect marker fires
/// on the transmute inside `AtomicPtr::new`. Confirms the test program
/// reliably surfaces the side effect — a "pure" outcome in the variant
/// tests below means the marker did the suppression.
#[test]
fn atomic_ptr_new_unmarked_is_impure() {
    InlineTestBuilder::new(ATOMIC_PROGRAM)
        .with_dependency_environment(stdlib_env())
        .check_ctrl(|ctrl| {
            ctrl.show_side_effects(true);
            ctrl.assert_purity(false);
        });
}

/// Anchor on the alias `AtomicPtr`. The resolver normalizes the alias to
/// its target `Atomic<*mut T>` and uses `[*mut T]` (with `T` as a `Param`)
/// to filter `inherent_impls(Atomic)` down to the AtomicPtr inherent
/// impl. The marker binds; the auto-marker is suppressed.
#[test]
fn atomic_ptr_new_marker_on_alias_binds() {
    InlineTestBuilder::new(ATOMIC_PROGRAM)
        .with_dependency_environment(stdlib_env())
        .with_marker_file(Path::new("tests/purity/atomic-via-alias-markers.toml"))
        .check_ctrl(|ctrl| {
            ctrl.show_side_effects(true);
            ctrl.assert_purity(true);
        });
}

/// Anchor on the underlying `Atomic` struct with an explicit turbofish
/// (`Atomic::<*mut u8>::new`). The resolver extracts `[*mut u8]` from the
/// segment's generic args and filters impls by `Self`-type match (Param
/// in the impl side acts as wildcard); only `Atomic<*mut T>::new` matches.
#[test]
fn atomic_ptr_new_marker_on_struct_with_turbofish_binds() {
    InlineTestBuilder::new(ATOMIC_PROGRAM)
        .with_dependency_environment(stdlib_env())
        .with_marker_file(Path::new(
            "tests/purity/atomic-via-struct-explicit-generics-markers.toml",
        ))
        .check_ctrl(|ctrl| {
            ctrl.show_side_effects(true);
            ctrl.assert_purity(true);
        });
}

/// Anchor on the underlying `Atomic` struct with no generic args
/// (`Atomic::new`). Without a disambiguating signal, the resolver falls
/// back to `find_map` first-match across the 12 `Atomic<X>` inherent
/// impls — nondeterministic but observed to pick `Atomic<bool>::new`.
/// The actual call site `Atomic<*mut u8>::new` has a different `DefId`
/// and remains uncovered, so the transmute still surfaces. Pins the
/// documented limitation at `utils/resolve.rs:360`.
#[test]
fn atomic_ptr_new_marker_on_struct_no_generics_is_ambiguous() {
    InlineTestBuilder::new(ATOMIC_PROGRAM)
        .with_dependency_environment(stdlib_env())
        .with_marker_file(Path::new("tests/purity/atomic-via-struct-markers.toml"))
        .check_ctrl(|ctrl| {
            ctrl.show_side_effects(true);
            ctrl.assert_purity(false);
        });
}
