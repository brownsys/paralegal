//! `<std::path::Path as std::cmp::PartialEq>::eq` used to fail with
//! `NoImplsFound` because `core::cmp::PartialEq` resolves as both the
//! trait (the actual one — has impls) and the derive macro re-export
//! (no impls). The resolver's `find` on `module_children` picked the
//! macro, so `for_each_relevant_impl` had nothing to iterate.
//!
//! The fix in `non_local_item_children_by_name` prefers non-macro
//! candidates when the same name appears in multiple namespaces. This
//! test pins that the marker now binds cleanly.

use paralegal_flow::test_utils::{
    DependencyEnvironment, DependencyEnvironmentBuilder, InlineTestBuilder,
};
use std::path::Path;
use std::sync::OnceLock;

static STDLIB_ENV: OnceLock<DependencyEnvironment> = OnceLock::new();

fn stdlib_env() -> &'static DependencyEnvironment {
    STDLIB_ENV.get_or_init(|| {
        DependencyEnvironmentBuilder::new()
            .with_stdlib()
            .with_extra_args(["--side-effect-markers", "--include-std"])
            .build()
    })
}

/// Compiles with `_internal_can_fail_resolve_silently = false`. Pre-fix
/// the marker file resolved to the derive-macro re-export of
/// `PartialEq`, producing `NoImplsFound` and a hard compile error;
/// post-fix the trait wins, `for_each_relevant_impl` returns the impl
/// set, and compilation succeeds.
#[test]
fn path_eq_marker_resolves_to_trait_not_macro() {
    InlineTestBuilder::new(stringify!(
        fn main() {
            let _ = std::path::Path::new("a") == std::path::Path::new("b");
        }
    ))
    .with_dependency_environment(stdlib_env())
    .with_marker_file(Path::new("tests/purity/path-eq-markers.toml"))
    .check_ctrl(|_| {});
}
