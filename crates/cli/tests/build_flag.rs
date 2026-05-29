//! Integration tests for `cargo paralegal-flow`'s `--cargo-subcommand`
//! flag and the artifact-discovery logic that supports it.
//!
//! Each test runs the analyser against a checked-in fixture crate
//! (`tests/fixtures/<name>/`) that hides a paralegal marker behind an
//! `#[paralegal::analyze]` entrypoint, then asserts the marker shows
//! up in the produced PDG. A missing marker implies the cli failed to
//! find the `.fgo` for the crate's compilation unit — the regression
//! we're guarding against.
//!
//! The three layouts (bin-only, lib-only, lib+bin) are each exercised
//! twice: once with the cli's default (`check`, backward-compat
//! baseline) and once with `--cargo-subcommand build` (the new path
//! that produces a runnable binary as a side effect of analysis).
//!
//! Multiple tests target the same fixture, so the helper serialises
//! tests-per-fixture via a mutex. Tests against different fixtures
//! still run in parallel.
//!
//! Not covered here:
//!   * Workspaces with multiple member crates — `--target` filtering
//!     already has light coverage in the paralegal-flow tests.
//!   * Multiple `[[bin]]` targets in one crate — same shape as lib+bin
//!     from the cli's perspective.
//!   * Crates with `build.rs` — build-script artifacts arrive as
//!     `BuildScriptExecuted`, not `CompilerArtifact`, so they never
//!     enter the cli's filter.

mod helpers;

use helpers::Test;

// --- build mode ----------------------------------------------------------

#[test]
fn bin_only_build_finds_marker() {
    let analysis = Test::bin_only()
        .unwrap()
        .cargo_subcommand("build")
        .analyze()
        .unwrap();
    analysis.assert_marker("bin_marker");
}

#[test]
fn lib_only_build_finds_marker() {
    let analysis = Test::lib_only()
        .unwrap()
        .cargo_subcommand("build")
        .analyze()
        .unwrap();
    analysis.assert_marker("lib_marker");
}

#[test]
fn lib_and_bin_build_finds_both_markers() {
    let analysis = Test::lib_and_bin()
        .unwrap()
        .cargo_subcommand("build")
        .analyze()
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
    let analysis = Test::bin_only().unwrap().analyze().unwrap();
    analysis.assert_marker("bin_marker");
}

#[test]
fn lib_only_check_finds_marker() {
    let analysis = Test::lib_only().unwrap().analyze().unwrap();
    analysis.assert_marker("lib_marker");
}

#[test]
fn lib_and_bin_check_finds_both_markers() {
    let analysis = Test::lib_and_bin().unwrap().analyze().unwrap();
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
/// to filter fresh artifacts away, the second `analyze()` would
/// either bail in the helper (empty `paralegal-artifact.json`) or
/// drop the marker.
#[test]
fn rerun_under_build_keeps_artifact_populated() {
    let test = Test::bin_only().unwrap().cargo_subcommand("build");
    let first = test.analyze().unwrap();
    first.assert_marker("bin_marker");
    let second = test.analyze().unwrap();
    second.assert_marker("bin_marker");
}
