use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_middle::ty::TyCtxt;
use rustc_utils::cache::Cache;

pub struct BodyCache<'tcx> {
    tcx: TyCtxt<'tcx>,
    load_policy: Box<dyn Fn(CrateNum) -> bool + 'tcx>,
    cache: Cache<DefId, BodyWithBorrowckFacts<'tcx>>,
}

impl<'tcx> BodyCache<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, policy: impl Fn(CrateNum) -> bool + 'tcx) -> Self {
        Self {
            tcx,
            cache: Default::default(),
            load_policy: Box::new(policy),
        }
    }

    pub fn get(&self, key: DefId) -> Option<&BodyWithBorrowckFacts<'tcx>> {
        if (self.load_policy)(key.krate) {}
    }
}
