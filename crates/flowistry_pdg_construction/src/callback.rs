//! CAllbacks to influence graph construction and their supporting types.

use flowistry_pdg::{rustc_portable::Location, CallString};
use rustc_middle::mir::Place;

use crate::FnResolution;

pub trait CallChangeCallback<'tcx> {
    fn on_inline(&self, info: CallInfo<'tcx>) -> CallChanges<'tcx>;

    fn on_inline_miss(
        &self,
        _resolution: FnResolution<'tcx>,
        _loc: Location,
        _under_analysis: FnResolution<'tcx>,
        _call_string: Option<CallString>,
        _reason: InlineMissReason,
    ) {
    }
}

pub struct CallChangeCallbackFn<'tcx> {
    f: Box<dyn Fn(CallInfo<'tcx>) -> CallChanges<'tcx> + 'tcx>,
}

impl<'tcx> CallChangeCallbackFn<'tcx> {
    pub fn new(f: impl Fn(CallInfo<'tcx>) -> CallChanges<'tcx> + 'tcx) -> Self {
        Self { f: Box::new(f) }
    }
}

impl<'tcx> CallChangeCallback<'tcx> for CallChangeCallbackFn<'tcx> {
    fn on_inline(&self, info: CallInfo<'tcx>) -> CallChanges<'tcx> {
        (self.f)(info)
    }
}

#[derive(Debug)]
pub enum InlineMissReason {
    Async(String),
}

impl Default for CallChanges<'_> {
    fn default() -> Self {
        CallChanges {
            skip: SkipCall::NoSkip,
            fake_effects: vec![],
        }
    }
}

/// Information about the function being called.
pub struct CallInfo<'tcx> {
    /// The potentially-monomorphized resolution of the callee.
    pub callee: FnResolution<'tcx>,

    /// If the callee is an async closure created by an `async fn`, this is the
    /// `async fn` item.
    pub async_parent: Option<FnResolution<'tcx>>,

    /// The call-stack up to the current call site.
    pub call_string: CallString,

    /// Would the PDG for this function be served from the cache.
    pub is_cached: bool,
}

/// A fake effect to insert into the PDG upon a function call.
#[derive(Debug)]
pub struct FakeEffect<'tcx> {
    /// The place (in the *callee*!) subject to a fake effect.
    pub place: Place<'tcx>,

    /// The kind of fake effect to insert into the PDG.
    pub kind: FakeEffectKind,
}

/// The kind of fake effect to insert into the PDG.
#[derive(Debug)]
pub enum FakeEffectKind {
    /// A fake read to an argument of a function call.
    ///
    /// For example, a fake read to argument `_1` of the call `f(_5)`
    /// would add an edge `_5@main::fcall -> _1@main->f::START`.
    Read,

    /// A fake write to an argument of a function call.
    ///
    /// For example, a fake write to argument `(*_1)` of the call `f(&mut _5)`
    /// would add an edge `_5@main::<before> -> _5@main::fcall`.
    Write,
}

/// User-provided changes to the default PDG construction behavior for function calls.
///
/// Construct [`CallChanges`] via [`CallChanges::default`].
#[derive(Debug)]
pub struct CallChanges<'tcx> {
    pub(crate) skip: SkipCall,
    fake_effects: Vec<FakeEffect<'tcx>>,
}

/// Whether or not to skip recursing into a function call during PDG construction.
#[derive(Debug)]
pub enum SkipCall {
    /// Skip the function, and perform a modular approxmation of its effects.
    Skip,

    /// Recurse into the function as normal.
    NoSkip,
}

impl<'tcx> CallChanges<'tcx> {
    /// Inidicate whether or not to skip recursing into the given function.
    pub fn with_skip(self, skip: SkipCall) -> Self {
        CallChanges { skip, ..self }
    }

    /// Provide a set of fake effect to insert into the PDG.
    pub fn with_fake_effects(self, fake_effects: Vec<FakeEffect<'tcx>>) -> Self {
        CallChanges {
            fake_effects,
            ..self
        }
    }
}
