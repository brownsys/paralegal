/// This module contains tests for the purity analysis feature. These tests are
/// basically verbatim copies of the tests from scrutinizer.
///
/// many tests have been commented out because paralegal is missing certain
/// features that scrutinizer has.
// Ignored for now because it needs an external crate.
// mod foreign;
mod atomic_alias;
mod leaky;
mod misc;
mod path_eq_resolver;
mod raw_ptr;
mod recursive;
mod side_effects;
mod r#static;

use paralegal_flow::test_utils::{DependencyEnvironment, DependencyEnvironmentBuilder};
use std::sync::OnceLock;

static STDLIB_ENV: OnceLock<DependencyEnvironment> = OnceLock::new();

pub(super) fn stdlib_environment() -> &'static DependencyEnvironment {
    STDLIB_ENV.get_or_init(|| {
        DependencyEnvironmentBuilder::new()
            .with_extra_args(["--side-effect-markers", "--include-std"])
            .with_markers("tests/purity/stdlib-markers.toml")
            .with_manifest("tests/purity/test-crate-std/Cargo.toml")
            .with_stdlib()
            .build()
    })
}
