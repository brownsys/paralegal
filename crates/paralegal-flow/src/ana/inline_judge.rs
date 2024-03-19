use flowistry_pdg_construction::CallInfo;
use paralegal_spdg::Identifier;
use rustc_utils::cache::Cache;

use crate::{
    args::InliningDepth,
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
        }
    }

    /// Should we perform inlining on this function?
    pub fn should_inline(&self, info: &CallInfo<'tcx>) -> bool {
        match self.analysis_control.inlining_depth() {
            _ if self.function_has_markers(info.callee) => false,
            InliningDepth::Adaptive => self.marker_ctx.marker_is_reachable(info.callee),
            InliningDepth::Fixed(limit) => {
                debug_assert!(!info.call_string.is_empty());
                info.call_string.len() <= *limit as usize
            }
            InliningDepth::Unconstrained => true,
        }
    }
}
