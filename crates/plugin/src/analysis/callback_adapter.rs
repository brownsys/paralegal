//! Bridge between [`InlineJudge`] (paralegal-side policy) and the Flowistry
//! [`CallChangeCallback`] interface that drives `MemoPdgConstructor`.
//!
//! Also hosts the [`Stub`] inherent methods that translate a stub annotation
//! into a concrete [`Instance`] + [`CallingConvention`] for the constructor
//! to consume.

use std::rc::Rc;

use rustc_hir as hir;
use rustc_middle::{
    mir::Location,
    ty::{Instance, TyCtxt, TypingEnv},
};
use rustc_span::{ErrorGuaranteed, Span as RustSpan, Symbol};
use tracing::debug;

use crate::{
    args::Stub,
    callback::{CallChangeCallback, CallChanges, CallInfo, InlineMissReason, SkipCall},
    utils::{ArgSlice, type_as_fn},
};

use super::{
    CallingConvention,
    inline_judge::{InlineJudge, InlineJudgement, K},
};

pub(super) struct MyCallback<'tcx> {
    judge: Rc<InlineJudge<'tcx>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> MyCallback<'tcx> {
    pub(super) fn new(judge: Rc<InlineJudge<'tcx>>, tcx: TyCtxt<'tcx>) -> Self {
        Self { judge, tcx }
    }
}

impl Stub {
    pub fn resolve_alternate_instance<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        function: Instance<'tcx>,
        param_env: TypingEnv<'tcx>,
        at: RustSpan,
    ) -> Result<Instance<'tcx>, ErrorGuaranteed> {
        match self {
            Stub::SubClosure { generic_name } | Stub::SubFuture { generic_name } => {
                let name = Symbol::intern(generic_name);
                let generics = tcx.generics_of(function.def_id());
                let Some(param_index) = (0..generics.count()).find(|&idx| {
                    let param = generics.param_at(idx, tcx);
                    param.name == name
                }) else {
                    return Err(tcx.dcx().span_err(
                        at,
                        format!("Function has no parameter named {generic_name}"),
                    ));
                };
                let ty = function.args[param_index].expect_ty();
                let (def_id, args) = type_as_fn(tcx, ty).unwrap();
                Ok(Instance::expect_resolve(tcx, param_env, def_id, args, at))
            }
        }
    }

    fn indirect_required(
        &self,
        tcx: TyCtxt,
        def_id: hir::def_id::DefId,
        at: RustSpan,
    ) -> Result<bool, ErrorGuaranteed> {
        let bool = match self {
            Stub::SubClosure { .. } => {
                use rustc_hir::def::DefKind;
                match tcx.def_kind(def_id) {
                    DefKind::Closure => true,
                    DefKind::Fn => false,
                    kind => {
                        return Err(tcx.dcx().span_err(
                            at,
                            format!("Expected `fn` or `closure` def kind, got {kind:?}"),
                        ));
                    }
                }
            }
            Stub::SubFuture { .. } => {
                assert!(tcx.coroutine_is_async(def_id));
                true
            }
        };
        Ok(bool)
    }

    /// Performs the effects of this model on the provided function.
    ///
    /// `function` is what was to be called but for which a stub exists,
    /// `arguments` are the arguments to that call.
    ///
    /// Returns a new instance to call instead and how it should be called.
    pub fn apply<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        function: Instance<'tcx>,
        param_env: TypingEnv<'tcx>,
        arguments: ArgSlice<'_, 'tcx>,
        at: RustSpan,
    ) -> Result<(Instance<'tcx>, CallingConvention<'tcx>), ErrorGuaranteed> {
        let instance = self.resolve_alternate_instance(tcx, function, param_env, at)?;
        let def_id = instance.def_id();

        let expect_indirect = self.indirect_required(tcx, def_id, at)?;
        let poll = tcx.lang_items().poll();
        let calling_convention = if expect_indirect {
            let clj = match arguments {
                [clj] => clj,
                [r#gen, _]
                    if tcx.def_kind(function.def_id()) == hir::def::DefKind::AssocFn
                        && tcx.associated_item(function.def_id()).trait_item_def_id() == poll =>
                {
                    r#gen
                }
                _ => {
                    return Err(tcx.dcx().span_err(
                        at,
                        format!(
                            "this function ({:?}) should have only one argument but it has {}",
                            function.def_id(),
                            arguments.len()
                        ),
                    ));
                }
            };
            CallingConvention::Indirect {
                shim: None,
                closure_arg: clj.clone(),
                // This is incorrect, but we only support
                // non-argument closures at the moment so this
                // will never be used.
                tupled_arguments: clj.clone(),
            }
        } else {
            CallingConvention::Direct(arguments.into())
        };
        Ok((instance, calling_convention))
    }
}

impl<'tcx> CallChangeCallback<'tcx, K> for MyCallback<'tcx> {
    fn on_inline(&self, info: CallInfo<'tcx, '_, K>) -> CallChanges<'tcx, K> {
        let changes = CallChanges::default();

        let judgement = self.judge.should_inline(&info);
        debug!(
            "Judgement for {}: {judgement}",
            self.tcx.def_path_str(info.callee.def_id())
        );

        let skip = match judgement {
            InlineJudgement::AbstractViaType(_) => SkipCall::Skip,
            InlineJudgement::UseStub(model) => {
                if let Ok((instance, calling_convention)) = model.apply(
                    self.tcx,
                    info.callee,
                    info.param_env,
                    info.arguments,
                    info.span,
                ) {
                    SkipCall::Replace {
                        instance,
                        calling_convention,
                        cache_key: *info.cache_key,
                    }
                } else {
                    SkipCall::Skip
                }
            }
            InlineJudgement::Inline(advance_k) => SkipCall::NoSkip(if advance_k {
                *info.cache_key + 1
            } else {
                *info.cache_key
            }),
        };
        changes.with_skip(skip)
    }

    fn on_inline_miss(
        &self,
        resolution: Instance<'tcx>,
        param_env: TypingEnv<'tcx>,
        _loc: Location,
        _parent: Instance<'tcx>,
        reason: InlineMissReason,
        call_span: rustc_span::Span,
    ) {
        self.judge.ensure_is_safe_to_approximate(
            param_env,
            resolution,
            call_span,
            false,
            match reason {
                InlineMissReason::Async(_) => "async",
                InlineMissReason::TraitMethod => "virtual trait method",
            },
        );
    }

    fn root_k(&self, _info: Instance<'tcx>) -> K {
        0
    }
}
