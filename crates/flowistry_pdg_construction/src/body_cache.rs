use std::{fs::File, io::Read, path::PathBuf};

use flowistry::mir::FlowistryInput;
use polonius_engine::FactTypes;
use rustc_borrowck::consumers::{ConsumerOptions, RustcFacts};

use rustc_hir::{
    def_id::{CrateNum, DefId},
    intravisit::{self, nested_filter::NestedFilter},
};
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::{
    hir::{map::Map, nested_filter::OnlyBodies},
    mir::{Body, ClearCrossCrate},
    ty::TyCtxt,
};
use rustc_serialize::{Decodable, Encodable};
use rustc_utils::cache::Cache;

use crate::encoder::{ParalegalDecoder, ParalegalEncoder};

#[derive(TyDecodable, TyEncodable, Debug)]
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

#[derive(Debug, Encodable, Decodable)]
pub struct FlowistryFacts {
    pub subset_base: Vec<(
        <RustcFacts as FactTypes>::Origin,
        <RustcFacts as FactTypes>::Origin,
        <RustcFacts as FactTypes>::Point,
    )>,
}

pub type LocationIndex = <RustcFacts as FactTypes>::Point;

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

struct VisitFilter;

impl<'hir> NestedFilter<'hir> for VisitFilter {
    type Map = Map<'hir>;

    const INTER: bool = true;
    const INTRA: bool = true;
}

struct DumpingVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    target_dir: PathBuf,
}

impl<'tcx> intravisit::Visitor<'tcx> for DumpingVisitor<'tcx> {
    type NestedFilter = OnlyBodies;
    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_fn(
        &mut self,
        function_kind: intravisit::FnKind<'tcx>,
        function_declaration: &'tcx rustc_hir::FnDecl<'tcx>,
        body_id: rustc_hir::BodyId,
        _: rustc_span::Span,
        local_def_id: rustc_hir::def_id::LocalDefId,
    ) {
        let mut body_with_facts = rustc_borrowck::consumers::get_body_with_borrowck_facts(
            self.tcx,
            local_def_id,
            ConsumerOptions::PoloniusInputFacts,
        );

        for scope in body_with_facts.body.source_scopes.iter_mut() {
            scope.local_data = ClearCrossCrate::Clear;
        }

        let to_write = CachedBody {
            body: body_with_facts.body,
            input_facts: FlowistryFacts {
                subset_base: body_with_facts.input_facts.unwrap().subset_base,
            },
        };

        let dir = &self.target_dir;
        let path = dir.join(
            self.tcx
                .def_path(local_def_id.to_def_id())
                .to_filename_friendly_no_crate(),
        );

        if !dir.exists() {
            std::fs::create_dir(dir).unwrap();
        }

        let mut encoder = ParalegalEncoder::new(&path, self.tcx);

        to_write.encode(&mut encoder);
        encoder.finish();

        intravisit::walk_fn(
            self,
            function_kind,
            function_declaration,
            body_id,
            local_def_id,
        )
    }
}

pub fn dump_mir_and_borrowck_facts(tcx: TyCtxt) {
    let mut vis = DumpingVisitor {
        tcx,
        target_dir: intermediate_out_dir(tcx),
    };
    tcx.hir().visit_all_item_likes_in_crate(&mut vis);
}

const INTERMEDIATE_ARTIFACT_EXT: &str = "bwbf";

fn compute_body_with_borrowck_facts(tcx: TyCtxt<'_>, def_id: DefId) -> CachedBody<'_> {
    let paths = if def_id.is_local() {
        vec![intermediate_out_dir(tcx)]
    } else {
        tcx.crate_extern_paths(def_id.krate)
            .iter()
            .map(|p| p.with_extension(INTERMEDIATE_ARTIFACT_EXT))
            .collect()
    };
    for path in &paths {
        let path = path.join(tcx.def_path(def_id).to_filename_friendly_no_crate());
        let Ok(mut file) = File::open(path) else {
            continue;
        };
        let mut buf = Vec::new();
        file.read_to_end(&mut buf).unwrap();
        let mut decoder = ParalegalDecoder::new(tcx, buf.as_slice());
        let meta = CachedBody::decode(&mut decoder);
        return meta;
    }

    panic!("No facts for {def_id:?} found at any path tried: {paths:?}");
}

/// Create the name of the file in which to store intermediate artifacts.
///
/// HACK(Justus): `TyCtxt::output_filenames` returns a file stem of
/// `lib<crate_name>-<hash>`, whereas `OutputFiles::with_extension` returns a file
/// stem of `<crate_name>-<hash>`. I haven't found a clean way to get the same
/// name in both places, so i just assume that these two will always have this
/// relation and prepend the `"lib"` here.
fn intermediate_out_dir(tcx: TyCtxt) -> PathBuf {
    let rustc_out_file = tcx
        .output_filenames(())
        .with_extension(INTERMEDIATE_ARTIFACT_EXT);
    let dir = rustc_out_file
        .parent()
        .unwrap_or_else(|| panic!("{} has no parent", rustc_out_file.display()));
    let file = rustc_out_file
        .file_name()
        .unwrap_or_else(|| panic!("has no file name"))
        .to_str()
        .unwrap_or_else(|| panic!("not utf8"));

    let file = if file.starts_with("lib") {
        std::borrow::Cow::Borrowed(file)
    } else {
        format!("lib{file}").into()
    };

    dir.join(file.as_ref())
}
