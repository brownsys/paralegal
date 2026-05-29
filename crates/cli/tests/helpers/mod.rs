//! Test harness for cli integration tests that drive `cargo paralegal-flow`
//! over a checked-in fixture crate and inspect the produced PDG(s).
//!
//! Differs from [`crates/policy/tests/helpers/mod.rs`] in two ways:
//!   * Supports bin-only and lib+bin fixtures, not just lib — the
//!     `--cargo-subcommand` flag and `locate_bin_fgo` logic under test
//!     diverge from check-mode behaviour only on bin targets.
//!   * Returns the loaded [`ProgramDescription`]s directly (one per
//!     `target` in `paralegal-artifact.json`) instead of going through
//!     `paralegal_policy::GraphLocation`. The policy crate's loader
//!     bails on more than one target (`Loading more than one graph is
//!     not currently supported`, see policy/src/lib.rs), which is
//!     exactly the shape the lib+bin case produces.
//!
//! Fixtures live in `tests/fixtures/<name>/` as real on-disk cargo
//! crates (workspace-excluded so the outer workspace doesn't try to
//! compile them). Multiple tests target the same fixture, so each
//! [`Test`] takes a per-fixture mutex on construction and runs
//! `cargo clean` to start from a known state; tests against different
//! fixtures still run in parallel.

#![allow(dead_code)]

use std::{
    collections::HashMap,
    fs,
    path::{Path, PathBuf},
    sync::{LazyLock, Mutex, MutexGuard, OnceLock},
};

use anyhow::{ensure, Result};
use paralegal_pdg::utils::{prepare_analyzer_command, CommandFactory};
use paralegal_pdg::{
    FileSystemStorable, Identifier, ParalegalArtifact, ProgramDescription, ARTIFACT_NAME,
};

/// Lazily build `cargo-paralegal-flow` + `paralegal-flow-impl` once per
/// test process; cuts the per-test setup cost from "rebuild the
/// analyser" to "spawn a process".
static ANALYZER_COMMAND: LazyLock<CommandFactory> =
    LazyLock::new(|| prepare_analyzer_command(Path::new("../..")).unwrap());

/// Per-fixture-path mutex map. Concurrent tests on the same fixture
/// serialize on its mutex (they share Cargo.toml + target/); tests on
/// different fixtures stay parallel.
///
/// Mutexes are leaked into `'static` so the `MutexGuard` a `Test`
/// holds doesn't have to borrow from anything fixture-shaped.
fn fixture_lock(path: &Path) -> MutexGuard<'static, ()> {
    static LOCKS: OnceLock<Mutex<HashMap<PathBuf, &'static Mutex<()>>>> = OnceLock::new();
    let map = LOCKS.get_or_init(|| Mutex::new(HashMap::new()));
    let mu = {
        let mut g = map.lock().expect("fixture-lock map poisoned");
        *g.entry(path.to_owned())
            .or_insert_with(|| Box::leak(Box::new(Mutex::new(()))))
    };
    // A poisoned per-fixture mutex just means a previous test panicked
    // mid-run; the on-disk state will be cleaned by `Test::new` anyway,
    // so unwrap-into-inner gives us a fresh guard.
    mu.lock().unwrap_or_else(|e| e.into_inner())
}

/// Builder for one fixture run. Holds the fixture's mutex for the
/// lifetime of the test so the on-disk Cargo state isn't raced by
/// other tests against the same fixture.
#[must_use]
pub struct Test {
    fixture_path: PathBuf,
    cargo_subcommand: Option<&'static str>,
    _lock: MutexGuard<'static, ()>,
}

impl Test {
    pub fn bin_only() -> Result<Self> {
        Self::for_fixture("bin-only")
    }

    pub fn lib_only() -> Result<Self> {
        Self::for_fixture("lib-only")
    }

    pub fn lib_and_bin() -> Result<Self> {
        Self::for_fixture("lib-and-bin")
    }

    fn for_fixture(name: &str) -> Result<Self> {
        let fixture_path = fixtures_root().join(name);
        ensure!(
            fixture_path.join("Cargo.toml").is_file(),
            "fixture {} has no Cargo.toml at {}",
            name,
            fixture_path.display()
        );
        let lock = fixture_lock(&fixture_path);
        // Reset to a known state at test entry. `cargo clean` clears
        // target/ but not the cli's outputs at the crate root, so we
        // hand-remove those too.
        cargo_clean(&fixture_path)?;
        Ok(Self {
            fixture_path,
            cargo_subcommand: None,
            _lock: lock,
        })
    }

    /// Pass `--cargo-subcommand <sub>` to `cargo paralegal-flow`.
    /// Unset leaves the cli's own default (`check`) in effect.
    pub fn cargo_subcommand(mut self, sub: &'static str) -> Self {
        self.cargo_subcommand = Some(sub);
        self
    }

    /// On-disk crate directory. For tests that want to inspect or
    /// mutate the workspace between repeated analyser invocations.
    pub fn workspace(&self) -> &Path {
        &self.fixture_path
    }

    /// Run `cargo paralegal-flow` over the fixture and load every PDG
    /// listed in `paralegal-artifact.json`. Call repeatedly within
    /// one test to exercise rerun behaviour — the fixture is cleaned
    /// only once, by [`Test::for_fixture`].
    pub fn analyze(&self) -> Result<Analysis> {
        self.invoke_analyzer()?;
        let artifact_path = self.fixture_path.join(ARTIFACT_NAME);
        let artifact = ParalegalArtifact::load(&artifact_path).map_err(|e| {
            anyhow::anyhow!(
                "loading {} after analyser run: {e}",
                artifact_path.display()
            )
        })?;
        ensure!(
            !artifact.targets.is_empty(),
            "analyser produced an empty paralegal-artifact.json — \
             no .fgo paths were collected from cargo's CompilerArtifact \
             stream. With `--cargo-subcommand build` this usually means \
             the bin-fallback in cli/src/main.rs::locate_bin_fgo failed."
        );
        let descriptions = artifact
            .targets
            .iter()
            .map(|p| ProgramDescription::canonical_read(p))
            .collect::<Result<Vec<_>>>()?;
        Ok(Analysis {
            artifact_paths: artifact.targets,
            descriptions,
        })
    }

    fn invoke_analyzer(&self) -> Result<()> {
        let mut cmd = ANALYZER_COMMAND.make();
        if let Some(sub) = self.cargo_subcommand {
            cmd.args(["--cargo-subcommand", sub]);
        }
        cmd.current_dir(&self.fixture_path);
        let status = cmd.status()?;
        ensure!(status.success(), "cargo paralegal-flow failed: {status}");
        Ok(())
    }
}

fn cargo_clean(fixture_path: &Path) -> Result<()> {
    let status = std::process::Command::new("cargo")
        .arg("clean")
        .current_dir(fixture_path)
        .status()?;
    ensure!(
        status.success(),
        "cargo clean failed in {}",
        fixture_path.display()
    );
    // `cargo clean` only nukes target/; the cli also writes these at the
    // crate root and we want a clean slate so the post-run reads see
    // outputs from this invocation, not the previous one.
    for name in [
        ARTIFACT_NAME,
        "flow-graph.stat.json",
        "flow-graph.marker_stats.json",
    ] {
        let _ = fs::remove_file(fixture_path.join(name));
    }
    Ok(())
}

/// Loaded PDGs for the fixture's `paralegal-artifact.json` targets.
pub struct Analysis {
    /// `.fgo` paths the cli wrote into `paralegal-artifact.json`.
    pub artifact_paths: Vec<PathBuf>,
    /// One [`ProgramDescription`] per `.fgo`. For LibOnly / BinOnly
    /// this is always length 1; for LibAndBin it's 2 (one per
    /// compilation unit).
    pub descriptions: Vec<ProgramDescription>,
}

impl Analysis {
    /// True if any `DefInfo` in any of the loaded descriptions carries
    /// a `#[paralegal::marker(<name>)]` annotation. Function-level
    /// markers live in `def_info[id].markers` (`MarkerAnnotation` per
    /// `#[paralegal::marker(...)]`), not in `SPDG.markers` (which is
    /// the per-node store used for type-derived / propagated markers).
    pub fn has_marker(&self, name: &str) -> bool {
        let want = Identifier::new_intern(name);
        self.descriptions.iter().any(|desc| {
            desc.def_info
                .values()
                .flat_map(|info| info.markers.iter())
                .any(|ann| ann.marker == want)
        })
    }

    /// Convenience assertion with a more useful failure message than
    /// `assert!(self.has_marker(name))` would give.
    pub fn assert_marker(&self, name: &str) {
        if !self.has_marker(name) {
            let all: std::collections::BTreeSet<String> = self
                .descriptions
                .iter()
                .flat_map(|d| {
                    d.def_info
                        .values()
                        .flat_map(|info| info.markers.iter())
                        .map(|ann| ann.marker)
                })
                .map(|id| id.as_str().to_string())
                .collect();
            panic!(
                "expected marker `{name}` in produced graph but it was missing; \
                 saw {} description(s), markers present: {:?}",
                self.descriptions.len(),
                all
            );
        }
    }
}

fn fixtures_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
}
