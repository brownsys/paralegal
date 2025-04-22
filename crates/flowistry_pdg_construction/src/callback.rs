//! Callbacks to influence graph construction and their supporting types.

use flowistry_pdg::{rustc_portable::Location, CallString};

use rustc_middle::{
    mir::{self, Operand},
    ty::{Instance, ParamEnv},
};
use rustc_span::Span;

use crate::calling_convention::CallingConvention;

pub trait CallChangeCallback<'tcx, K> {
    fn on_inline(&self, info: CallInfo<'tcx, '_, K>) -> CallChanges<'tcx, K>;

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

    fn root_k(&self, info: Instance<'tcx>) -> K;
}

pub struct DefaultCallback;

impl<'tcx, K: Default> CallChangeCallback<'tcx, K> for DefaultCallback {
    fn on_inline(&self, _info: CallInfo<'tcx, '_, K>) -> CallChanges<'tcx, K> {
        CallChanges::default()
    }

    fn root_k(&self, info: Instance<'tcx>) -> K {
        Default::default()
    }
}

pub struct CallChangeCallbackFn<'tcx, K> {
    f: Box<dyn Fn(CallInfo<'tcx, '_, K>) -> CallChanges<'tcx, K> + 'tcx>,
}

impl<'tcx, K> CallChangeCallbackFn<'tcx, K> {
    pub fn new(f: impl Fn(CallInfo<'tcx, '_, K>) -> CallChanges<'tcx, K> + 'tcx) -> Self {
        Self { f: Box::new(f) }
    }
}

impl<'tcx, K: Default> CallChangeCallback<'tcx, K> for CallChangeCallbackFn<'tcx, K> {
    fn on_inline(&self, info: CallInfo<'tcx, '_, K>) -> CallChanges<'tcx, K> {
        (self.f)(info)
    }

    fn root_k(&self, info: Instance<'tcx>) -> K {
        Default::default()
    }
}

#[derive(Debug)]
pub enum InlineMissReason {
    Async(String),
    TraitMethod,
}

impl<'tcx, K: Default> Default for CallChanges<'tcx, K> {
    fn default() -> Self {
        CallChanges {
            skip: SkipCall::NoSkip(Default::default()),
        }
    }
}

/// Information about the function being called.
pub struct CallInfo<'tcx, 'mir, K> {
    /// The potentially-monomorphized resolution of the callee.
    pub callee: Instance<'tcx>,

    pub cache_key: &'mir K,

    /// If the callee is an async closure created by an `async fn`, this is the
    /// `async fn` item.
    pub async_parent: Option<Instance<'tcx>>,

    /// The current location
    pub call_string: Location,

    pub span: Span,

    pub arguments: &'mir [Operand<'tcx>],

    pub caller_body: &'mir mir::Body<'tcx>,
    pub param_env: ParamEnv<'tcx>,
}

/// User-provided changes to the default PDG construction behavior for function calls.
///
/// Construct [`CallChanges`] via [`CallChanges::default`].
#[derive(Debug)]
pub struct CallChanges<'tcx, K> {
    pub(crate) skip: SkipCall<'tcx, K>,
}

/// Whether or not to skip recursing into a function call during PDG construction.
#[derive(Debug)]
pub enum SkipCall<'tcx, K> {
    /// Skip the function, and perform a modular approxmation of its effects.
    Skip,

    /// Recurse into the function as normal.
    NoSkip(K),

    /// Replace with a call to this other function and arguments.
    Replace {
        instance: Instance<'tcx>,
        calling_convention: CallingConvention<'tcx>,
        cache_key: K,
    },
}

impl<'tcx, K> CallChanges<'tcx, K> {
    /// Indicate whether or not to skip recursing into the given function.
    pub fn with_skip(self, skip: SkipCall<'tcx, K>) -> Self {
        CallChanges { skip }
    }
}
