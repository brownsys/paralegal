//! Hook points for embedding paralegal as a library inside another rustc
//! driver (e.g. haven). An extension's [`pre_pdg`] hook runs after MIR is
//! borrow-checked but before paralegal consumes it for PDG construction.
//!
//! [`pre_pdg`]: DriverExtension::pre_pdg
//!
//! Extensions are plugged in via [`crate::run_with_extension`]. The standalone
//! `paralegal_flow` binary uses [`NoopExtension`].
//!
//! The interface is deliberately minimal: one hook, with [`MarkerCtx`] exposed
//! so extensions can query side-effect/safety markers without re-running
//! marker discovery. Add further hooks only when a concrete consumer needs
//! them.
//!
//! Stability: this is a paralegal-internal interface tracked alongside the
//! paralegal-pinned nightly. It is not a stable plugin ABI.
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_session::Session;

use crate::MarkerCtx;

pub trait DriverExtension: Send {
    /// Runs after MIR borrow-check completes and `MarkerCtx` is populated,
    /// before paralegal starts PDG construction. Implementations may mutate
    /// MIR via the steal/return pattern on the relevant rustc queries.
    ///
    /// Always fires on the analyzed crate. Whether it fires on dependency
    /// crates that are compiled-and-dumped is gated by
    /// [`Self::requires_dependency_markers`] — constructing `MarkerCtx` for
    /// every dependency is non-trivial work that paralegal otherwise skips.
    fn pre_pdg<'tcx>(&mut self, _tcx: TyCtxt<'tcx>, _markers: &MarkerCtx<'tcx>) {}

    /// If true, `pre_pdg` fires on dependency crates too (those handled by
    /// [`crate::CrateHandling::CompileAndDump`]) and paralegal forces full
    /// `MarkerDatabase::init` for them. Default `false` to preserve the
    /// standalone paralegal cost profile when no real extension is loaded.
    fn requires_dependency_markers(&self) -> bool {
        false
    }

    /// Optional `fn` to layer on top of paralegal's own [`Providers`]
    /// overrides during [`rustc_interface::Config`] setup. Paralegal installs
    /// its own `mir_borrowck` wrapper first, then calls the extension's `fn`
    /// (if any) so extensions can replace or further wrap the providers.
    ///
    /// Returns a plain `fn` rather than a closure because rustc's
    /// `Config::override_queries` itself is `Option<fn(..)>`. Extensions that
    /// need to thread per-invocation state must stash it in a `OnceLock` /
    /// thread-local before `run_with_extension` is called.
    fn query_providers(&self) -> Option<fn(&Session, &mut Providers)> {
        None
    }
}

/// Default extension used when paralegal runs standalone. All hooks are
/// no-ops; `requires_dependency_markers` returns `false`.
pub struct NoopExtension;

impl DriverExtension for NoopExtension {}
