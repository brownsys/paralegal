use crate::{mir::Place, utils::FnResolution, AnalysisCtrl, DefId, MarkerCtx, TyCtxt};

/// The interpretation of marker placement as it pertains to inlining and inline
/// elision.
///
/// [`MarkerCtx`] provides the information on which this judge bases its
/// decisions. It also takes into account whether the respective configuration
/// options have been set.
pub struct InlineJudge<'tcx> {
    marker_ctx: MarkerCtx<'tcx>,
    tcx: TyCtxt<'tcx>,
    analysis_control: &'static AnalysisCtrl,
}

impl<'tcx> InlineJudge<'tcx> {
    /// Looking at the dependencies and type alone, do we think this function
    /// performs side effects?
    fn probably_performs_side_effects(
        &self,
        func: FnResolution<'tcx>,
        args: &[Option<Place<'tcx>>],
        place_has_dependencies: impl Fn(Place<'tcx>) -> bool,
    ) -> bool {
        let has_no_input_deps = || !args.iter().cloned().flatten().any(place_has_dependencies);
        let Ok(sig) = func.sig(self.tcx) else {
            return true;
        };

        let has_no_outputs =
            sig.output().is_unit() && !sig.inputs().iter().any(|i| i.is_mutable_ptr());
        has_no_outputs || has_no_input_deps()
    }

    /// Is it safe to elide this function, e.g. abstract by its dataflow effects
    /// alone?
    pub fn can_be_elided(
        &self,
        function: FnResolution<'tcx>,
        args: &[Option<Place<'tcx>>],
        place_has_dependencies: impl Fn(Place<'tcx>) -> bool,
    ) -> bool {
        self.analysis_control.avoid_inlining()
            && !self.function_has_markers(function)
            && !self.marker_is_reachable(function.def_id())
            && !self.probably_performs_side_effects(function, args, place_has_dependencies)
    }

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

    /// Is a marker reachable from this item?
    fn marker_is_reachable(&self, def_id: DefId) -> bool {
        self.marker_ctx.marker_is_reachable(def_id)
    }

    pub fn context(&self) -> &MarkerCtx<'tcx> {
        &self.marker_ctx
    }
}
