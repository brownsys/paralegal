use crate::{
    mir::Place,
    utils::{FnResolution, IntoBodyId},
    DefId, LocalDefId, MarkerCtx, TyCtxt,
};

pub struct InlineJudge<'tcx> {
    marker_ctx: MarkerCtx<'tcx>,
    tcx: TyCtxt<'tcx>,
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
        has_no_outputs || args.iter().cloned().flatten().any(place_has_dependencies)
    }

    pub fn can_be_elided(
        &self,
        func: DefId,
        args: &[Option<Place<'tcx>>],
        place_has_dependencies: impl Fn(Place<'tcx>) -> bool,
    ) -> bool {
        debug!("Checking if {func:?} can be elided");
        !self.marker_ctx.marker_is_reachable(func)
            && !self.probably_performs_side_effects(func, &args, place_has_dependencies)
    }

    pub fn new(marker_ctx: MarkerCtx<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self { marker_ctx, tcx }
    }

    pub fn should_inline(&self, function: FnResolution<'tcx>) -> bool {
        self.marker_ctx
            .all_function_markers(function)
            .next()
            .is_none()
    }

    pub fn marker_is_reachable(&self, def_id: DefId) -> bool {
        self.marker_ctx.marker_is_reachable(def_id)
    }
}
