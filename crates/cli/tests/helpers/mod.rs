//! Test harness for cli integration tests that drive `cargo paralegal-flow`
//! over a small on-disk fixture and inspect the produced PDGs.
//!
//! Differs from [`crates/policy/tests/helpers/mod.rs`] in two ways:
//!   * Supports bin-only and lib+bin crate layouts, not just lib — the
//!     `--cargo-subcommand` flag and `locate_bin_fgo` logic under test
//!     only diverge from check-mode behaviour on bin targets.
//!   * Returns the loaded [`ProgramDescription`]s directly (one per
//!     `target` in `paralegal-artifact.json`) instead of going through
//!     `paralegal_policy::GraphLocation`. The policy crate's loader
//!     bails on more than one target (`Loading more than one graph is
//!     not currently supported`, see policy/src/lib.rs), which is
//!     exactly the shape the lib+bin case produces.
//!
//! The Cargo.toml + sources are written directly (no `cargo init` +
//! `cargo add`) so a single fixture can declare both `src/lib.rs` and
//! `src/main.rs` and exercise the lib+bin path in one analyser run.

#![allow(dead_code)]

use std::{
    env, fs,
    path::{Path, PathBuf},
    sync::LazyLock,
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

/// Shape of the fixture crate. Drives which source files get written.
#[derive(Clone, Copy)]
pub enum CrateLayout {
    BinOnly,
    LibOnly,
    LibAndBin,
}

/// Builder for one fixture run.
#[must_use]
pub struct Test {
    layout: CrateLayout,
    lib_source: Option<String>,
    bin_source: Option<String>,
    /// `None` leaves the cli at its default (`check`).
    cargo_subcommand: Option<&'static str>,
    tempdir: PathBuf,
    cleanup: bool,
}

impl Test {
    pub fn bin_only(src: impl Into<String>) -> Result<Self> {
        Self::new(CrateLayout::BinOnly, None, Some(src.into()))
    }

    pub fn lib_only(src: impl Into<String>) -> Result<Self> {
        Self::new(CrateLayout::LibOnly, Some(src.into()), None)
    }

    pub fn lib_and_bin(lib_src: impl Into<String>, bin_src: impl Into<String>) -> Result<Self> {
        Self::new(
            CrateLayout::LibAndBin,
            Some(lib_src.into()),
            Some(bin_src.into()),
        )
    }

    fn new(
        layout: CrateLayout,
        lib_source: Option<String>,
        bin_source: Option<String>,
    ) -> Result<Self> {
        let tempdir = temporary_directory()?;
        println!("Test fixture at {}", tempdir.display());
        Ok(Self {
            layout,
            lib_source,
            bin_source,
            cargo_subcommand: None,
            tempdir,
            cleanup: true,
        })
    }

    /// Pass `--cargo-subcommand <sub>` to `cargo paralegal-flow`.
    /// Unset leaves the cli's own default in effect.
    pub fn cargo_subcommand(mut self, sub: &'static str) -> Self {
        self.cargo_subcommand = Some(sub);
        self
    }

    /// Keep the tempdir on disk after `run`/`analyze`. Useful when
    /// debugging a failing assertion locally.
    pub fn with_cleanup(mut self, cleanup: bool) -> Self {
        self.cleanup = cleanup;
        self
    }

    /// On-disk crate directory. Useful for tests that mutate the
    /// workspace between repeated analyser invocations.
    pub fn workspace(&self) -> &Path {
        &self.tempdir
    }

    /// Run `cargo paralegal-flow` over the fixture, load every PDG
    /// listed in `paralegal-artifact.json`, return them. The caller
    /// inspects markers / shapes via [`Analysis`].
    pub fn run(self) -> Result<Analysis> {
        let analysis = self.analyze()?;
        if self.cleanup {
            let _ = fs::remove_dir_all(&self.tempdir);
        }
        Ok(analysis)
    }

    /// Stage + invoke + load, but skip cleanup. Useful for the rerun
    /// test that wants to invoke the analyser twice against the same
    /// on-disk state without re-staging.
    pub fn analyze(&self) -> Result<Analysis> {
        self.populate_fixture()?;
        self.invoke_analyzer()?;
        let artifact_path = self.tempdir.join(ARTIFACT_NAME);
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

    pub fn invoke_analyzer(&self) -> Result<()> {
        self.populate_fixture()?;
        let mut cmd = ANALYZER_COMMAND.make();
        if let Some(sub) = self.cargo_subcommand {
            cmd.args(["--cargo-subcommand", sub]);
        }
        cmd.current_dir(&self.tempdir);
        let status = cmd.status()?;
        ensure!(status.success(), "cargo paralegal-flow failed: {status}");
        Ok(())
    }

    /// Idempotent: writes Cargo.toml and the chosen source files.
    fn populate_fixture(&self) -> Result<()> {
        fs::create_dir_all(self.tempdir.join("src"))?;
        let paralegal_lib_path = workspace_root().join("crates").join("paralegal");
        ensure!(
            paralegal_lib_path.exists(),
            "paralegal helper crate not found at {}",
            paralegal_lib_path.display()
        );
        let manifest = format!(
            r#"[package]
name = "cli-test-fixture"
version = "0.0.0"
edition = "2021"

[dependencies]
paralegal = {{ path = "{}" }}
"#,
            paralegal_lib_path.display()
        );
        fs::write(self.tempdir.join("Cargo.toml"), manifest)?;

        // Cargo's default target inference picks up `src/lib.rs` and
        // `src/main.rs` automatically, so for any layout we just write
        // the files the layout calls for. BinOnly omits src/lib.rs;
        // LibOnly omits src/main.rs; LibAndBin writes both.
        if let Some(lib) = self.lib_source.as_ref() {
            fs::write(self.tempdir.join("src").join("lib.rs"), lib)?;
        } else {
            let _ = fs::remove_file(self.tempdir.join("src").join("lib.rs"));
        }
        if let Some(bin) = self.bin_source.as_ref() {
            fs::write(self.tempdir.join("src").join("main.rs"), bin)?;
        } else {
            let _ = fs::remove_file(self.tempdir.join("src").join("main.rs"));
        }
        Ok(())
    }
}

impl Drop for Test {
    fn drop(&mut self) {
        if self.cleanup {
            let _ = fs::remove_dir_all(&self.tempdir);
        }
    }
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

fn workspace_root() -> PathBuf {
    // CARGO_MANIFEST_DIR for cli/tests/ is the cli crate root;
    // two levels up is the paralegal workspace root.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .canonicalize()
        .expect("workspace root canonicalises")
}

fn temporary_directory() -> Result<PathBuf> {
    let tmp = env::temp_dir();
    loop {
        let name: u32 = rand::random();
        let path = tmp.join(format!("paralegal-cli-test-{name:x}"));
        if !path.exists() {
            fs::create_dir(&path)?;
            return Ok(path);
        }
    }
}
