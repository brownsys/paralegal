//! CAllbacks to influence graph construction and their supporting types.

use flowistry_pdg::{rustc_portable::Location, CallString};
use rustc_middle::ty::Instance;

pub trait CallChangeCallback<'tcx> {
    fn on_inline(&self, info: CallInfo<'tcx>) -> CallChanges;

    fn on_inline_miss(
        &self,
        _resolution: Instance<'tcx>,
        _loc: Location,
        _under_analysis: Instance<'tcx>,
        _reason: InlineMissReason,
    ) {
    }
}

pub struct CallChangeCallbackFn<'tcx> {
    f: Box<dyn Fn(CallInfo<'tcx>) -> CallChanges + 'tcx>,
}

impl<'tcx> CallChangeCallbackFn<'tcx> {
    pub fn new(f: impl Fn(CallInfo<'tcx>) -> CallChanges + 'tcx) -> Self {
        Self { f: Box::new(f) }
    }
}

impl<'tcx> CallChangeCallback<'tcx> for CallChangeCallbackFn<'tcx> {
    fn on_inline(&self, info: CallInfo<'tcx>) -> CallChanges {
        (self.f)(info)
    }
}

#[derive(Debug)]
pub enum InlineMissReason {
    Async(String),
}

impl Default for CallChanges {
    fn default() -> Self {
        CallChanges {
            skip: SkipCall::NoSkip,
        }
    }
}

/// Information about the function being called.
pub struct CallInfo<'tcx> {
    /// The potentially-monomorphized resolution of the callee.
    pub callee: Instance<'tcx>,

    /// If the callee is an async closure created by an `async fn`, this is the
    /// `async fn` item.
    pub async_parent: Option<Instance<'tcx>>,

    /// The call-stack up to the current call site.
    pub call_string: CallString,

    /// Would the PDG for this function be served from the cache.
    pub is_cached: bool,
}

/// User-provided changes to the default PDG construction behavior for function calls.
///
/// Construct [`CallChanges`] via [`CallChanges::default`].
#[derive(Debug)]
pub struct CallChanges {
    pub(crate) skip: SkipCall,
}

/// Whether or not to skip recursing into a function call during PDG construction.
#[derive(Debug)]
pub enum SkipCall {
    /// Skip the function, and perform a modular approxmation of its effects.
    Skip,

    /// Recurse into the function as normal.
    NoSkip,
}

impl CallChanges {
    /// Inidicate whether or not to skip recursing into the given function.
    pub fn with_skip(self, skip: SkipCall) -> Self {
        CallChanges { skip }
    }
}
