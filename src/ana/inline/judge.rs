use crate::{mir::Place, utils::FnResolution, AnalysisCtrl, DefId, MarkerCtx, TyCtxt};

pub struct InlineJudge<'tcx> {
    marker_ctx: MarkerCtx<'tcx>,
    tcx: TyCtxt<'tcx>,
    analysis_control: &'static AnalysisCtrl,
}

impl<'tcx> InlineJudge<'tcx> {
    fn probably_performs_side_effects(
        &self,
        func: DefId,
        args: &[Option<Place<'tcx>>],
        place_has_dependencies: impl Fn(Place<'tcx>) -> bool,
    ) -> bool {
        let sig = self.tcx.fn_sig(func).skip_binder().skip_binder();
        let has_no_outputs =
            sig.output().is_unit() && !sig.inputs().iter().any(|i| i.is_mutable_ptr());
        has_no_outputs || !args.iter().cloned().flatten().any(place_has_dependencies)
    }

    pub fn can_be_elided(
        &self,
        function: FnResolution<'tcx>,
        args: &[Option<Place<'tcx>>],
        place_has_dependencies: impl Fn(Place<'tcx>) -> bool,
    ) -> bool {
        self.analysis_control.avoid_inlining()
            && !self.function_has_markers(function)
            && !self.marker_is_reachable(function.def_id())
            && !self.probably_performs_side_effects(function.def_id(), args, place_has_dependencies)
    }

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

    pub fn should_inline(&self, function: FnResolution<'tcx>) -> bool {
        self.analysis_control.use_recursive_analysis() && !self.function_has_markers(function)
    }

    fn marker_is_reachable(&self, def_id: DefId) -> bool {
        self.marker_ctx.marker_is_reachable(def_id)
    }
}
