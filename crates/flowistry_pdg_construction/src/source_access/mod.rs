use std::{
    cell::RefCell,
    fs::File,
    io::BufWriter,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use tracing::debug;

use paralegal_flowistry::mir::FlowistryInput;

use polonius_engine::FactTypes;
use rustc_borrowck::consumers::{BodyWithBorrowckFacts, ConsumerOptions, RustcFacts};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::{
    def_id::{CrateNum, DefId, DefIndex, LocalDefId, LOCAL_CRATE},
    intravisit::{self},
};
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::{
    hir::nested_filter::OnlyBodies,
    mir::{
        coverage::{BlockMarkerId, CoverageKind},
        pretty::MirWriter,
        Body, ClearCrossCrate, Statement, StatementKind,
    },
    ty::TyCtxt,
    util::Providers,
};

use paralegal_rustc_utils::cache::Cache;
use rustc_type_ir::RegionVid;

mod encoder;

use encoder::{decode_from_file, encode_to_file};

pub use encoder::{ParalegalDecoder, ParalegalEncoder};

/// A mir [`Body`] and all the additional borrow checking facts that our
/// points-to analysis needs.
#[derive(TyDecodable, TyEncodable, Debug)]
pub struct CachedBody<'tcx> {
    body: Body<'tcx>,
    input_facts: FlowistryFacts,
}

const REPLACEMENT_STATEMENT: StatementKind<'static> =
    StatementKind::Coverage(CoverageKind::BlockMarker {
        id: BlockMarkerId::MAX,
    });

fn for_each_reachable_statement<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    mut f: impl FnMut(&mut Statement<'tcx>),
) {
    for id in tcx.nested_bodies_within(def_id).iter().chain([def_id]) {
        let (mir, promoted) = tcx.mir_promoted(id);
        let mut slf_guard = mir.risky_hack_borrow_mut();
        let mut promoted_guard = promoted.risky_hack_borrow_mut();
        let target_bodies = std::iter::once(&mut *slf_guard).chain(promoted_guard.iter_mut());
        target_bodies
            .flat_map(|b| b.basic_blocks_mut().iter_mut())
            .flat_map(|bb| bb.statements.iter_mut())
            .for_each(&mut f);
    }
}

fn with_incompatible_instructions_removed<'tcx, R>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    f: impl FnOnce() -> R,
) -> R {
    let mut original_statements = vec![];
    for_each_reachable_statement(tcx, def_id, |stmt| {
        let tcx_scoped_replacement_statement =
            unsafe { std::mem::transmute::<_, StatementKind<'tcx>>(REPLACEMENT_STATEMENT) };
        let kind = &mut stmt.kind;
        assert_ne!(kind, &tcx_scoped_replacement_statement);
        if matches!(kind, StatementKind::BackwardIncompatibleDropHint { .. }) {
            original_statements.push(std::mem::replace(kind, tcx_scoped_replacement_statement));
        }
    });
    let res = f();
    original_statements.reverse();
    for_each_reachable_statement(tcx, def_id, |stmt| {
        let kind = &mut stmt.kind;
        if kind == &unsafe { std::mem::transmute::<_, StatementKind<'tcx>>(REPLACEMENT_STATEMENT) }
        {
            *kind = original_statements.pop().unwrap();
        }
    });
    res
}

fn get_bodies_associated_with<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<(CachedBody<'tcx>, Vec<(LocalDefId, CachedBody<'tcx>)>)> {
    let mut root_id = def_id;
    while tcx.is_closure_like(root_id.into()) {
        root_id = tcx.parent(root_id.into()).expect_local();
    }
    let (mir, _) = tcx.mir_promoted(root_id);

    if mir.borrow().should_skip() {
        tracing::debug!(
            "Skipping body for {} (custom mir)",
            tcx.def_path_str(def_id)
        );
        return None;
    }
    // let target_name =
    //     "<unix::linux_like::linux_l4re_shared::__c_anonymous_ifr_ifru as core::fmt::Debug>::fmt";
    // let actual_name = tcx.def_path_str(def_id);
    // if target_name == actual_name {
    //     let writer = MirWriter::new(tcx);
    //     let path = "offending-function.mir";
    //     let f = File::create(path).unwrap();
    //     tracing::info!(
    //         "Dumping {} to {}",
    //         actual_name,
    //         Path::new(path).canonicalize().unwrap().display()
    //     );
    //     let mut w = BufWriter::new(f);
    //     writer.write_mir_fn(&mir.borrow(), &mut w).unwrap();
    // }
    //tracing::debug!("Checking body `{}`", tcx.def_path_str(def_id));
    // HACK: We remove all BackwardIncompatibleDropHint instructions, because
    // they trigger an ICE when computing the borrowcheck instruction
    let mut bodies = with_incompatible_instructions_removed(tcx, def_id, || {
        rustc_borrowck::consumers::get_bodies_with_borrowck_facts(
            tcx,
            root_id,
            ConsumerOptions::PoloniusInputFacts,
        )
    });
    // MORE HACKS: we also clean the hacky instructions from our output to make sure they don't cause issues.
    for stmt in bodies
        .values_mut()
        .flat_map(|b| b.body.basic_blocks_mut().iter_mut())
        .flat_map(|bb| bb.statements.iter_mut())
    {
        let kind = &mut stmt.kind;
        if kind == &unsafe { std::mem::transmute::<_, StatementKind<'tcx>>(REPLACEMENT_STATEMENT) }
        {
            *kind = StatementKind::Nop;
        }
    }
    let slf = CachedBody::from_body(bodies.remove(&def_id).unwrap_or_else(|| {
        panic!(
            "Retrieving body of {} via borrowchecking {} failed",
            tcx.def_path_str(def_id),
            tcx.def_path_str(root_id)
        )
    }));

    Some((
        slf,
        bodies
            .drain()
            .map(|(id, b)| (id, CachedBody::from_body(b)))
            .collect(),
    ))
}

impl<'tcx> CachedBody<'tcx> {
    fn from_body(body_with_facts: BodyWithBorrowckFacts<'tcx>) -> Self {
        let mut body = body_with_facts.body;
        clean_undecodable_data_from_body(&mut body);

        Self {
            body,
            input_facts: FlowistryFacts {
                subset_base: body_with_facts
                    .input_facts
                    .as_ref()
                    .expect("polonius input must exist")
                    .subset_base
                    .iter()
                    .map(|&(v1, v2, _)| (v1.into(), v2.into()))
                    .collect(),
            },
        }
    }

    pub fn get_local(def_id: LocalDefId, tcx: TyCtxt<'tcx>) -> Option<&'tcx Self> {
        LOCAL_CACHE.with(move |cache| {
            let body = cache
                .try_retrieve_many(&def_id.local_def_index, true, move |_| {
                    let (res, others) = unsafe {
                        std::mem::transmute::<
                            (CachedBody<'tcx>, Vec<(LocalDefId, CachedBody<'tcx>)>),
                            (CachedBody<'static>, Vec<(LocalDefId, CachedBody<'static>)>),
                        >(get_bodies_associated_with(tcx, def_id)?)
                    };
                    Some((
                        res,
                        others
                            .into_iter()
                            .map(move |(id, b)| (id.local_def_index, b))
                            .collect(),
                    ))
                })
                .as_success();

            unsafe { std::mem::transmute::<Option<&_>, _>(body) }
        })
    }
}

pub fn mir_borrowck<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> rustc_middle::queries::mir_borrowck::ProvidedValue<'tcx> {
    CachedBody::get_local(def_id, tcx);
    let mut providers = Providers::default();
    rustc_borrowck::provide(&mut providers.queries);
    let original_mir_borrowck = providers.queries.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

impl<'tcx> FlowistryInput<'tcx, 'tcx> for &'tcx CachedBody<'tcx> {
    fn body(self) -> &'tcx Body<'tcx> {
        &self.body
    }

    fn input_facts_subset_base(self) -> Box<dyn Iterator<Item = (RegionVid, RegionVid)> + 'tcx> {
        Box::new(self.input_facts.subset_base.iter().copied())
    }
}

/// The subset of borrowcheck facts that the points-to analysis (flowistry)
/// needs.
#[derive(Debug, Encodable, Decodable)]
pub struct FlowistryFacts {
    pub subset_base: Vec<(RegionVid, RegionVid)>,
}

pub type LocationIndex = <RustcFacts as FactTypes>::Point;

thread_local! {
    static LOCAL_CACHE: Cache<DefIndex, CachedBody<'static>> = Cache::default();
}
type BodyMap<'tcx> = FxHashMap<DefIndex, CachedBody<'tcx>>;

/// Allows loading bodies from previosly written artifacts.
///
/// Ensure this cache outlives any flowistry analysis that is performed on the
/// bodies it returns or risk UB.
pub struct BodyCache<'tcx> {
    tcx: TyCtxt<'tcx>,
    cache: Cache<CrateNum, BodyMap<'tcx>>,
    timer: RefCell<Duration>,
    std_crates: Vec<CrateNum>,
}

pub fn std_crates(tcx: TyCtxt<'_>) -> impl Iterator<Item = CrateNum> + use<'_> {
    tcx.crates(()).iter().copied().filter(move |&c| {
        c != LOCAL_CRATE
            && tcx
                .crate_extern_paths(c)
                .iter()
                .all(|p| p.starts_with(tcx.sess.opts.sysroot.path()))
    })
}

impl<'tcx> BodyCache<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            cache: Default::default(),
            timer: RefCell::new(Duration::ZERO),
            std_crates: std_crates(tcx).collect(),
        }
    }

    pub fn timer(&self) -> Duration {
        *self.timer.borrow()
    }

    pub fn get(&self, key: DefId) -> &'tcx CachedBody<'tcx> {
        self.try_get(key).unwrap_or_else(|| {
            panic!(
                "INVARIANT VIOLATION: {} is not loadable",
                self.tcx.def_path_str(key)
            )
        })
    }

    /// Serve the body from the cache or read it from the disk.
    pub fn try_get(&self, key: DefId) -> Option<&'tcx CachedBody<'tcx>> {
        let body = if let Some(local) = key.as_local() {
            CachedBody::get_local(local, self.tcx)?
        } else if self.std_crates.contains(&key.krate) || self.tcx.is_foreign_item(key) {
            return None;
        } else {
            let res = self
                .cache
                .get(&key.krate, |_| {
                    let result = load_body_and_facts(self.tcx, key.krate);
                    debug!(
                        "Loaded {} bodies from {}",
                        result.len(),
                        self.tcx.crate_name(key.krate)
                    );
                    result
                })
                .get(&key.index)
                .unwrap_or_else(|| {
                    panic!("INVARIANT VIOLATION: body map loaded but {key:?} not found")
                });
            res
        };

        // SAFETY: Theoretically this struct may not outlive the body, but
        // to simplify lifetimes flowistry uses 'tcx anywhere. But if we
        // actually try to provide that we're risking race conditions
        // (because it needs global variables like MIR_BODIES).
        //
        // So until we fix flowistry's lifetimes this is good enough.
        Some(unsafe { std::mem::transmute::<&CachedBody<'tcx>, &'tcx CachedBody<'tcx>>(body) })
    }
}

/// A visitor to collect all bodies in the crate and write them to disk.
struct DumpingVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    targets: Vec<LocalDefId>,
}

/// Some data in a [Body] is not cross-crate compatible. Usually because it
/// involves storing a [LocalDefId]. This function makes sure to sanitize those
/// out.
fn clean_undecodable_data_from_body(body: &mut Body) {
    for scope in body.source_scopes.iter_mut() {
        scope.local_data = ClearCrossCrate::Clear;
    }

    for stmt in body
        .basic_blocks_mut()
        .iter_mut()
        .flat_map(|bb| bb.statements.iter_mut())
    {
        if matches!(stmt.kind, StatementKind::FakeRead(_)) {
            stmt.make_nop(true)
        }
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for DumpingVisitor<'tcx> {
    type NestedFilter = OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_fn(
        &mut self,
        function_kind: intravisit::FnKind<'tcx>,
        function_declaration: &'tcx rustc_hir::FnDecl<'tcx>,
        body_id: rustc_hir::BodyId,
        _: rustc_span::Span,
        local_def_id: rustc_hir::def_id::LocalDefId,
    ) {
        self.targets.push(local_def_id);

        intravisit::walk_fn(
            self,
            function_kind,
            function_declaration,
            body_id,
            local_def_id,
        )
    }
}

/// A complete visit over the local crate items, collecting all bodies and
/// calculating the necessary borrowcheck facts to store for later points-to
/// analysis.
///
/// Ensure this gets called early in the compiler before the unoptimized mir
/// bodies are stolen.
pub fn dump_mir_and_borrowck_facts(tcx: TyCtxt<'_>) -> (Duration, Duration) {
    let mut vis = DumpingVisitor {
        tcx,
        targets: vec![],
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut vis);

    let tc_start = Instant::now();
    let targets = vis.targets.into_iter().collect::<FxHashSet<LocalDefId>>();

    let bodies: FxHashMap<DefIndex, &CachedBody> = targets
        .into_iter()
        .map(|t| (t.local_def_index, CachedBody::get_local(t, tcx).unwrap()))
        .collect();

    let tc_time = tc_start.elapsed();
    let dump_time = Instant::now();
    let path = intermediate_out_dir(tcx, INTERMEDIATE_ARTIFACT_EXT);
    encode_to_file(tcx, &path, &bodies);
    debug!("Dumped {} bodies to {}", bodies.len(), path.display());
    (tc_time, dump_time.elapsed())
}

const INTERMEDIATE_ARTIFACT_EXT: &str = "bwbf";

/// Get the path where artifacts from this crate would be stored. Unlike
/// [`TyCtxt::crate_extern_paths`] this function does not crash when supplied
/// with [`LOCAL_CRATE`].
pub fn local_or_remote_paths(krate: CrateNum, tcx: TyCtxt, ext: &str) -> Vec<PathBuf> {
    if krate == LOCAL_CRATE {
        vec![intermediate_out_dir(tcx, ext)]
    } else {
        tcx.crate_extern_paths(krate)
            .iter()
            .map(|p| p.with_extension(ext))
            .collect()
    }
}

/// Try to load a [`CachedBody`] for this id.
fn load_body_and_facts(tcx: TyCtxt<'_>, krate: CrateNum) -> BodyMap<'_> {
    let paths = local_or_remote_paths(krate, tcx, INTERMEDIATE_ARTIFACT_EXT);
    for target_path in &paths {
        if !target_path.exists() {
            continue;
        }

        let data = decode_from_file(tcx, target_path).unwrap();
        return data;
    }

    panic!(
        "No facts for {:?} found at any path tried: {paths:?}",
        tcx.crate_name(krate)
    );
}

/// Create the name of the file in which to store intermediate artifacts.
///
/// HACK(Justus): `TyCtxt::output_filenames` returns a file stem of
/// `lib<crate_name>-<hash>`, whereas `OutputFiles::with_extension` returns a file
/// stem of `<crate_name>-<hash>`. I haven't found a clean way to get the same
/// name in both places, so i just assume that these two will always have this
/// relation and prepend the `"lib"` here.
pub fn intermediate_out_dir(tcx: TyCtxt, ext: &str) -> PathBuf {
    let rustc_out_file = tcx.output_filenames(()).with_extension(ext);
    let dir = rustc_out_file
        .parent()
        .unwrap_or_else(|| panic!("{} has no parent", rustc_out_file.display()));
    let file = rustc_out_file
        .file_name()
        .unwrap_or_else(|| panic!("has no file name"))
        .to_str()
        .unwrap_or_else(|| panic!("not utf8"));

    let file = format!("lib{file}");

    dir.join(file)
}
