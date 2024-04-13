use flowistry_pdg_construction::CallInfo;

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
        // Force for now so we can do sanity check on number of analyzed lines
        let _ = self
            .marker_ctx
            .has_transitive_reachable_markers(info.callee);
        match self.analysis_control.inlining_depth() {
            _ if self.marker_ctx.is_marked(info.callee.def_id())
                || !info.callee.def_id().is_local() =>
            {
                false
            }
            InliningDepth::Adaptive => self
                .marker_ctx
                .has_transitive_reachable_markers(info.callee),
            InliningDepth::Fixed(limit) => {
                debug_assert!(!info.call_string.is_empty());
                info.call_string.len() <= *limit as usize
            }
            InliningDepth::Unconstrained => true,
        }
    }

    pub fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        &self.marker_ctx
    }
}
