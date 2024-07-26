use flowistry::mir::FlowistryInput;
use polonius_engine::FactTypes;
use rustc_borrowck::consumers::RustcFacts;

use rustc_hir::def_id::{CrateNum, DefId};
use rustc_middle::{mir::Body, ty::TyCtxt};
use rustc_utils::{cache::Cache, mir::borrowck_facts::get_body_with_borrowck_facts};

use crate::nll_facts::{self, create_location_table, FlowistryFactSelection, FlowistryFacts};

pub struct CachedBody<'tcx> {
    body: Body<'tcx>,
    input_facts: FlowistryFacts,
}

impl<'tcx> FlowistryInput<'tcx> for &'tcx CachedBody<'tcx> {
    fn body(self) -> &'tcx Body<'tcx> {
        &self.body
    }

    fn input_facts_subset_base(
        self,
    ) -> &'tcx [(
        <RustcFacts as FactTypes>::Origin,
        <RustcFacts as FactTypes>::Origin,
        <RustcFacts as FactTypes>::Point,
    )] {
        &self.input_facts.subset_base
    }
}

/// Ensure this cache outlives any flowistry analysis that is performed on the
/// bodies it returns or risk UB.
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

    /// Set the policy for which crates should be loaded. It is inadvisable to
    /// change this after starting to call [get](Self::get).
    pub fn with_set_policy(&mut self, policy: impl Fn(CrateNum) -> bool + 'tcx) -> &mut Self {
        self.load_policy = Box::new(policy);
        self
    }

    pub fn get(&self, key: DefId) -> Option<&'tcx CachedBody<'tcx>> {
        (self.load_policy)(key.krate).then(|| {
            let cbody = self
                .cache
                .get(key, |_| compute_body_with_borrowck_facts(self.tcx, key));
            // SAFETY: Theoretically this struct may not outlive the body, but
            // to simplify lifetimes flowistry uses 'tcx anywhere. But if we
            // actually try to provide that we're risking race conditions
            // (because it needs global variables like MIR_BODIES).
            //
            // So until we fix flowistry's lifetimes this is good enough.
            unsafe { std::mem::transmute(cbody) }
        })
    }

    pub fn is_loadable(&self, key: DefId) -> bool {
        (self.load_policy)(key.krate)
    }
}

fn compute_body_with_borrowck_facts(tcx: TyCtxt<'_>, def_id: DefId) -> CachedBody<'_> {
    let body = tcx.optimized_mir(def_id).to_owned();
    if let Some(local) = def_id.as_local() {
        let local_facts = get_body_with_borrowck_facts(tcx, local);
        return CachedBody {
            body: local_facts.body.clone(),
            input_facts: FlowistryFactSelection {
                subset_base: local_facts
                    .input_facts
                    .as_ref()
                    .unwrap()
                    .subset_base
                    .clone(),
            },
        };
    };

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

    let facts = nll_facts::load_facts_for_flowistry(&location_table, &fact_file_for_item).unwrap();
    CachedBody {
        body,
        input_facts: facts,
    }
}
