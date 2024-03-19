use flowistry_pdg_construction::CallInfo;
use paralegal_spdg::Identifier;
use rustc_utils::cache::Cache;

use std::borrow::Cow;

use crate::{
    args::InliningDepth,
    ty,
    utils::FnResolution,
    utils::{AsFnAndArgs, TyCtxtExt},
    AnalysisCtrl, Either, MarkerCtx, TyCtxt,
};

/// The interpretation of marker placement as it pertains to inlining and inline
/// elision.
///
/// [`MarkerCtx`] provides the information on which this judge bases its
/// decisions. It also takes into account whether the respective configuration
/// options have been set.
pub struct InlineJudge<'tcx> {
    marker_ctx: MarkerCtx<'tcx>,
    #[allow(dead_code)]
    tcx: TyCtxt<'tcx>,
    analysis_control: &'static AnalysisCtrl,
    reachable_markers: Cache<FnResolution<'tcx>, Box<[Identifier]>>,
}

impl<'tcx> InlineJudge<'tcx> {
    /// Are there any markers on this function (direct or output type)?
    fn function_has_markers(&self, function: FnResolution<'tcx>) -> bool {
        self.marker_ctx
            .all_function_markers(function)
            .next()
            .is_some()
    }

    pub fn new(
        marker_ctx: MarkerCtx<'tcx>,
        tcx: TyCtxt<'tcx>,
        analysis_control: &'static AnalysisCtrl,
    ) -> Self {
        Self {
            marker_ctx,
            tcx,
            analysis_control,
            reachable_markers: Default::default(),
        }
    }

    fn get_reachable_markers(&self, function: FnResolution<'tcx>) -> &[Identifier] {
        self.reachable_markers.get(function, |_| {
            let mut self_markers = self
                .marker_ctx
                .all_function_markers(function)
                .map(|m| m.0.marker)
                .peekable();
            if self_markers.peek().is_some() {
                self_markers.collect()
            } else if let Some(local) = function.def_id().as_local() {
                let body = self.tcx.body_for_def_id(local).unwrap();
                body.body
                    .basic_blocks
                    .iter()
                    .flat_map(|bb| {
                        let term = bb.terminator();
                        let mono_term = match function {
                            FnResolution::Final(instance) => {
                                Cow::Owned(instance.subst_mir_and_normalize_erasing_regions(
                                    self.tcx,
                                    self.tcx.param_env(instance.def_id()),
                                    ty::EarlyBinder::bind(self.tcx.erase_regions(term.clone())),
                                ))
                            }
                            FnResolution::Partial(_) => Cow::Borrowed(term),
                        };
                        let Ok((fun, ..)) = mono_term.as_instance_and_args(self.tcx) else {
                            return Either::Left(std::iter::empty());
                        };
                        Either::Right(self.get_reachable_markers(fun).iter().copied())
                    })
                    .collect()
            } else {
                self_markers.collect()
            }
        })
    }

    fn marker_is_reachable(&self, function: FnResolution<'tcx>) -> bool {
        !self.get_reachable_markers(function).is_empty()
    }

    /// Should we perform inlining on this function?
    pub fn should_inline(&self, info: &CallInfo<'tcx>) -> bool {
        match self.analysis_control.inlining_depth() {
            _ if self.function_has_markers(info.callee) => false,
            InliningDepth::Adaptive => self.marker_is_reachable(info.callee),
            InliningDepth::Fixed(limit) => {
                debug_assert!(!info.call_string.is_empty());
                info.call_string.len() <= *limit as usize
            }
            InliningDepth::Unconstrained => true,
        }
    }
}
