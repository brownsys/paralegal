//! Callbacks to influence graph construction and their supporting types.

use flowistry_pdg::{rustc_portable::Location, CallString};

use rustc_middle::{
    mir::{self, Operand},
    ty::{Instance, ParamEnv},
};
use rustc_span::Span;

use crate::calling_convention::CallingConvention;

pub trait CallChangeCallback<'tcx> {
    fn on_inline(&self, info: CallInfo<'tcx, '_>) -> CallChanges<'tcx>;

    fn on_inline_miss(
        &self,
        _resolution: Instance<'tcx>,
        _param_env: ParamEnv<'tcx>,
        _loc: Location,
        _under_analysis: Instance<'tcx>,
        _reason: InlineMissReason,
        _call_span: Span,
    ) {
    }
}

pub struct CallChangeCallbackFn<'tcx> {
    f: Box<dyn Fn(CallInfo<'tcx, '_>) -> CallChanges<'tcx> + 'tcx>,
}

impl<'tcx> CallChangeCallbackFn<'tcx> {
    pub fn new(f: impl Fn(CallInfo<'tcx, '_>) -> CallChanges<'tcx> + 'tcx) -> Self {
        Self { f: Box::new(f) }
    }
}

impl<'tcx> CallChangeCallback<'tcx> for CallChangeCallbackFn<'tcx> {
    fn on_inline(&self, info: CallInfo<'tcx, '_>) -> CallChanges<'tcx> {
        (self.f)(info)
    }
}

#[derive(Debug)]
pub enum InlineMissReason {
    Async(String),
    TraitMethod,
}

impl<'tcx> Default for CallChanges<'tcx> {
    fn default() -> Self {
        CallChanges {
            skip: SkipCall::NoSkip,
        }
    }
}

/// Information about the function being called.
pub struct CallInfo<'tcx, 'mir> {
    /// The potentially-monomorphized resolution of the callee.
    pub callee: Instance<'tcx>,

    /// If the callee is an async closure created by an `async fn`, this is the
    /// `async fn` item.
    pub async_parent: Option<Instance<'tcx>>,

    /// The call-stack up to the current call site.
    pub call_string: CallString,

    /// Would the PDG for this function be served from the cache.
    pub is_cached: bool,

    pub span: Span,

    pub arguments: &'mir [Operand<'tcx>],

    pub caller_body: &'mir mir::Body<'tcx>,
    pub param_env: ParamEnv<'tcx>,
}

/// User-provided changes to the default PDG construction behavior for function calls.
///
/// Construct [`CallChanges`] via [`CallChanges::default`].
#[derive(Debug)]
pub struct CallChanges<'tcx> {
    pub(crate) skip: SkipCall<'tcx>,
}

/// Whether or not to skip recursing into a function call during PDG construction.
#[derive(Debug)]
pub enum SkipCall<'tcx> {
    /// Skip the function, and perform a modular approxmation of its effects.
    Skip,

    /// Recurse into the function as normal.
    NoSkip,

    /// Replace with a call to this other function and arguments.
    Replace {
        instance: Instance<'tcx>,
        calling_convention: CallingConvention<'tcx>,
    },
}

impl<'tcx> CallChanges<'tcx> {
    /// Indicate whether or not to skip recursing into the given function.
    pub fn with_skip(self, skip: SkipCall<'tcx>) -> Self {
        CallChanges { skip }
    }
}
