use std::cell::RefCell;

use polonius_engine::Output;
use rustc_borrowck::consumers::{BodyWithBorrowckFacts, PoloniusInput, RichLocation};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_middle::{
    mir::{Body, Location},
    ty::TyCtxt,
};
use rustc_utils::cache::{Cache, CopyCache};

use crate::nll_fact_parser::{self, create_location_table, CompressRichLocation, LocationIndex};

pub struct CachedBody<'tcx> {
    body: Body<'tcx>,
    input_facts: PoloniusInput,
}

pub struct BodyCache<'tcx> {
    tcx: TyCtxt<'tcx>,
    load_policy: Box<dyn Fn(CrateNum) -> bool + 'tcx>,
    cache: Cache<DefId, CachedBody<'tcx>>,
}

impl<'tcx> BodyCache<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, policy: impl Fn(CrateNum) -> bool + 'tcx) -> Self {
        Self {
            tcx,
            cache: Default::default(),
            load_policy: Box::new(policy),
        }
    }

    pub fn get(&self, key: DefId) -> Option<&CachedBody<'tcx>> {
        (self.load_policy)(key.krate).then(|| {
            self.cache
                .get(key, |_| compute_body_with_borrowck_facts(self.tcx, key))
        })
    }
}

fn compute_body_with_borrowck_facts<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> CachedBody<'tcx> {
    let body = tcx.optimized_mir(def_id).to_owned();

    let location_table = create_location_table(&body);

    let paths = tcx.crate_extern_paths(def_id.krate);

    let Some(nll_facts_dir) = paths.iter().find_map(|path| {
        let p = path.join("nll-facts");
        p.exists().then_some(p)
    }) else {
        panic!("No facts found at any path tried: {paths:?}");
    };

    let fact_file_for_item =
        nll_facts_dir.join(tcx.def_path(def_id).to_filename_friendly_no_crate());

    let facts =
        nll_fact_parser::load_tab_delimited_facts(&location_table, &fact_file_for_item).unwrap();
    CachedBody {
        body,
        input_facts: facts,
    }
}
