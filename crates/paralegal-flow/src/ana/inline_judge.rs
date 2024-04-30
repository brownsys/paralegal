use crate::{utils::FnResolution, AnalysisCtrl, MarkerCtx, TyCtxt};

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
    pub fn should_inline(&self, function: FnResolution<'tcx>) -> bool {
        self.analysis_control.use_recursive_analysis() && !self.function_has_markers(function)
    }

    pub fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        &self.marker_ctx
    }
}
