//! Integration tests for `cargo paralegal-flow`'s `--cargo-subcommand`
//! flag and the artifact-discovery logic that supports it.
//!
//! Each test stages a small fixture crate that hides a paralegal marker
//! behind an `#[paralegal::analyze]` entrypoint, runs the analyser, and
//! asserts the marker shows up in the produced PDG. A missing marker
//! implies the cli failed to find the `.fgo` for the crate's
//! compilation unit — the regression we're guarding against.
//!
//! The three layouts (bin-only, lib-only, lib+bin) are each exercised
//! twice: once with the cli's default (`check`, backward-compat
//! baseline) and once with `--cargo-subcommand build` (the new path
//! that produces a runnable binary as a side effect of analysis).
//!
//! Not covered here:
//!   * Workspaces with multiple member crates (case 6 in the design
//!     notes) — `--target` filtering already has light coverage in the
//!     paralegal-flow tests.
//!   * Multiple `[[bin]]` targets in one crate (case 5) — same shape
//!     as lib+bin from the cli's perspective.
//!   * Crates with `build.rs` (case 7) — build-script artifacts arrive
//!     as `BuildScriptExecuted`, not `CompilerArtifact`, so they never
//!     enter the cli's filter.

mod helpers;

use helpers::Test;

/// bin-only source: entrypoint calls a marked helper. Used by both
/// `bin_only_build_finds_marker` and `bin_only_check_finds_marker`.
const BIN_SOURCE: &str = r#"
#[paralegal::marker(bin_marker)]
fn marked_in_bin() {}

#[paralegal::analyze]
fn entrypoint() {
    marked_in_bin();
}

fn main() {
    entrypoint();
}
"#;

/// lib-only source: same idea, but the entrypoint is a free function
/// in `lib.rs` rather than `main`.
const LIB_SOURCE: &str = r#"
#[paralegal::marker(lib_marker)]
pub fn marked_in_lib() {}

#[paralegal::analyze]
pub fn lib_entrypoint() {
    marked_in_lib();
}
"#;

/// lib+bin sources. The lib hides one marker, the bin another; each
/// has its own `#[paralegal::analyze]` entrypoint so the analyser
/// produces a controller for each. The bin pulls the lib's symbol in
/// via `use` so the lib is actually linked into the bin's compile
/// graph (otherwise cargo wouldn't compile the lib at all under
/// `cargo build` of the bin).
const LIB_AND_BIN_LIB_SOURCE: &str = r#"
#[paralegal::marker(lib_marker)]
pub fn marked_in_lib() {}

#[paralegal::analyze]
pub fn lib_entrypoint() {
    marked_in_lib();
}
"#;

const LIB_AND_BIN_BIN_SOURCE: &str = r#"
use cli_test_fixture::lib_entrypoint;

#[paralegal::marker(bin_marker)]
fn marked_in_bin() {}

#[paralegal::analyze]
fn bin_entrypoint() {
    marked_in_bin();
    // Pull the lib into the bin's dep graph so cargo compiles it.
    lib_entrypoint();
}

fn main() {
    bin_entrypoint();
}
"#;

// --- build mode ----------------------------------------------------------

#[test]
fn bin_only_build_finds_marker() {
    let analysis = Test::bin_only(BIN_SOURCE)
        .unwrap()
        .cargo_subcommand("build")
        .run()
        .unwrap();
    analysis.assert_marker("bin_marker");
}

#[test]
fn lib_only_build_finds_marker() {
    let analysis = Test::lib_only(LIB_SOURCE)
        .unwrap()
        .cargo_subcommand("build")
        .run()
        .unwrap();
    analysis.assert_marker("lib_marker");
}

#[test]
fn lib_and_bin_build_finds_both_markers() {
    let analysis = Test::lib_and_bin(LIB_AND_BIN_LIB_SOURCE, LIB_AND_BIN_BIN_SOURCE)
        .unwrap()
        .cargo_subcommand("build")
        .run()
        .unwrap();
    // Two artifacts (lib + bin), each contributing its own marker.
    assert!(
        analysis.descriptions.len() >= 2,
        "expected ≥2 PDGs (lib + bin) under lib+bin layout, got {}",
        analysis.descriptions.len()
    );
    analysis.assert_marker("lib_marker");
    analysis.assert_marker("bin_marker");
}

// --- check mode (backward-compat baseline) -------------------------------

#[test]
fn bin_only_check_finds_marker() {
    let analysis = Test::bin_only(BIN_SOURCE).unwrap().run().unwrap();
    analysis.assert_marker("bin_marker");
}

#[test]
fn lib_only_check_finds_marker() {
    let analysis = Test::lib_only(LIB_SOURCE).unwrap().run().unwrap();
    analysis.assert_marker("lib_marker");
}

#[test]
fn lib_and_bin_check_finds_both_markers() {
    let analysis = Test::lib_and_bin(LIB_AND_BIN_LIB_SOURCE, LIB_AND_BIN_BIN_SOURCE)
        .unwrap()
        .run()
        .unwrap();
    assert!(analysis.descriptions.len() >= 2);
    analysis.assert_marker("lib_marker");
    analysis.assert_marker("bin_marker");
}

// --- rerun staleness -----------------------------------------------------

/// `cargo paralegal-flow build` followed by a second invocation
/// against the same workspace must still produce a populated
/// `paralegal-artifact.json` — cargo emits "fresh" `CompilerArtifact`
/// messages even when the compilation cache is hot, but the cli's
/// artifact collection has historically depended on that stream.
/// Regression bait: if cargo were to skip emission, or the cli were
/// to filter fresh artifacts away, the second `analyze()` call would
/// either bail in the helper (empty `paralegal-artifact.json`) or
/// drop the marker.
#[test]
fn rerun_under_build_keeps_artifact_populated() {
    let test = Test::bin_only(BIN_SOURCE)
        .unwrap()
        .cargo_subcommand("build")
        .with_cleanup(false);
    let first = test.analyze().unwrap();
    first.assert_marker("bin_marker");
    let second = test.analyze().unwrap();
    second.assert_marker("bin_marker");
}
