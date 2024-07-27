use std::rc::Rc;

use flowistry_pdg_construction::{body_cache::BodyCache, CallInfo};

use crate::{args::InliningDepth, AnalysisCtrl, MarkerCtx, TyCtxt};

#[derive(Clone)]
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
        let marker_target = info.async_parent.unwrap_or(info.callee);
        let marker_target_def_id = marker_target.def_id();
        match self.analysis_control.inlining_depth() {
            _ if self.marker_ctx.is_marked(marker_target_def_id) => false,
            InliningDepth::Adaptive => self
                .marker_ctx
                .has_transitive_reachable_markers(marker_target),
            InliningDepth::Shallow => false,
            InliningDepth::Unconstrained => true,
        }
    }

    pub fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        &self.marker_ctx
    }
}
