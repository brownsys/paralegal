use crate::{mir::Place, utils::IntoBodyId, DefId, LocalDefId, MarkerCtx, TyCtxt};

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
        if let Some(body_id) = func.into_body_id(self.tcx) {
            !self.marker_ctx.marker_is_reachable(body_id)
                && !self.probably_performs_side_effects(func, &args, place_has_dependencies)
        } else {
            false
        }
    }

    pub fn new(marker_ctx: MarkerCtx<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self { marker_ctx, tcx }
    }

    pub fn should_inline(&self, def_id: LocalDefId) -> bool {
        self.marker_ctx
            .all_function_markers(def_id.to_def_id())
            .next()
            .is_none()
    }

    pub fn marker_is_reachable(&self, def_id: LocalDefId) -> bool {
        self.marker_ctx
            .marker_is_reachable(def_id.into_body_id(self.tcx).unwrap())
    }
}
