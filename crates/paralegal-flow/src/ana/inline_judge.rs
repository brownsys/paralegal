use std::rc::Rc;

use flowistry_pdg_construction::{body_cache::BodyCache, CallInfo};
use rustc_hash::FxHashSet;
use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
use rustc_span::Symbol;

use crate::{ann::db::MarkerDatabase, args::InliningDepth, AnalysisCtrl, Args, MarkerCtx, TyCtxt};

/// The interpretation of marker placement as it pertains to inlining and inline
/// elision.
///
/// [`MarkerCtx`] provides the information on which this judge bases its
/// decisions. It also takes into account whether the respective configuration
/// options have been set.
pub struct InlineJudge<'tcx> {
    marker_ctx: MarkerCtx<'tcx>,
    analysis_control: &'static AnalysisCtrl,
    included_crates: FxHashSet<CrateNum>,
}

impl<'tcx> InlineJudge<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body_cache: Rc<BodyCache<'tcx>>, opts: &'static Args) -> Self {
        let included_crate_names = opts
            .anactrl()
            .included()
            .iter()
            .map(|s| Symbol::intern(s))
            .collect::<FxHashSet<_>>();
        let included_crates = tcx
            .crates(())
            .iter()
            .copied()
            .filter(|cnum| included_crate_names.contains(&tcx.crate_name(*cnum)))
            .chain(Some(LOCAL_CRATE))
            .collect::<FxHashSet<_>>();
        let marker_ctx =
            MarkerDatabase::init(tcx, opts, body_cache, included_crates.iter().copied()).into();
        Self {
            marker_ctx,
            included_crates,
            analysis_control: opts.anactrl(),
        }
    }

    pub fn included_crates(&self) -> &FxHashSet<CrateNum> {
        &self.included_crates
    }

    /// Should we perform inlining on this function?
    pub fn should_inline(&self, info: &CallInfo<'tcx>) -> bool {
        let marker_target = info.async_parent.unwrap_or(info.callee);
        let marker_target_def_id = marker_target.def_id();
        match self.analysis_control.inlining_depth() {
            _ if !self.included_crates.contains(&marker_target_def_id.krate)
                || self.marker_ctx.is_marked(marker_target_def_id) =>
            {
                false
            }
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
