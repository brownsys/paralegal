use std::path::PathBuf;

use flowistry::mir::FlowistryInput;

use polonius_engine::FactTypes;
use rustc_borrowck::consumers::{ConsumerOptions, RustcFacts};
use rustc_hir::{
    def_id::{CrateNum, DefId, LocalDefId, LOCAL_CRATE},
    intravisit::{self},
};
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::{
    hir::nested_filter::OnlyBodies,
    mir::{Body, ClearCrossCrate, StatementKind},
    ty::TyCtxt,
};

use rustc_utils::cache::Cache;

use crate::encoder::{decode_from_file, encode_to_file};

/// A mir [`Body`] and all the additional borrow checking facts that our
/// points-to analysis needs.
#[derive(TyDecodable, TyEncodable, Debug)]
pub struct CachedBody<'tcx> {
    body: Body<'tcx>,
    input_facts: FlowistryFacts,
}

impl<'tcx> CachedBody<'tcx> {
    /// Retrieve a body and the necessary facts for a local item.
    ///
    /// Ensure this is called early enough in the compiler
    /// (like `after_expansion`) so that the body has not been stolen yet.
    fn retrieve(tcx: TyCtxt<'tcx>, local_def_id: LocalDefId) -> Self {
        let mut body_with_facts = rustc_borrowck::consumers::get_body_with_borrowck_facts(
            tcx,
            local_def_id,
            ConsumerOptions::PoloniusInputFacts,
        );

        clean_undecodable_data_from_body(&mut body_with_facts.body);

        Self {
            body: body_with_facts.body,
            input_facts: FlowistryFacts {
                subset_base: body_with_facts.input_facts.unwrap().subset_base,
            },
        }
    }
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

/// The subset of borrowcheck facts that the points-to analysis (flowistry)
/// needs.
#[derive(Debug, Encodable, Decodable)]
pub struct FlowistryFacts {
    pub subset_base: Vec<(
        <RustcFacts as FactTypes>::Origin,
        <RustcFacts as FactTypes>::Origin,
        <RustcFacts as FactTypes>::Point,
    )>,
}

pub type LocationIndex = <RustcFacts as FactTypes>::Point;

/// Allows loading bodies from previosly written artifacts.
///
/// Ensure this cache outlives any flowistry analysis that is performed on the
/// bodies it returns or risk UB.
pub struct BodyCache<'tcx> {
    tcx: TyCtxt<'tcx>,
    cache: Cache<DefId, CachedBody<'tcx>>,
}

impl<'tcx> BodyCache<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            cache: Default::default(),
        }
    }

    /// Serve the body from the cache or read it from the disk.
    ///
    /// Returns `None` if the policy forbids loading from this crate.
    pub fn get(&self, key: DefId) -> &'tcx CachedBody<'tcx> {
        let cbody = self.cache.get(key, |_| load_body_and_facts(self.tcx, key));
        // SAFETY: Theoretically this struct may not outlive the body, but
        // to simplify lifetimes flowistry uses 'tcx anywhere. But if we
        // actually try to provide that we're risking race conditions
        // (because it needs global variables like MIR_BODIES).
        //
        // So until we fix flowistry's lifetimes this is good enough.
        unsafe { std::mem::transmute(cbody) }
    }
}

/// A visitor to collect all bodies in the crate and write them to disk.
struct DumpingVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    target_dir: PathBuf,
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
            stmt.make_nop()
        }
    }
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
        let to_write = CachedBody::retrieve(self.tcx, local_def_id);

        let dir = &self.target_dir;
        let path = dir.join(
            self.tcx
                .def_path(local_def_id.to_def_id())
                .to_filename_friendly_no_crate(),
        );

        if !dir.exists() {
            std::fs::create_dir(dir).unwrap();
        }

        encode_to_file(self.tcx, path, &to_write);

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
/// Ensure this gets called early in the compiler before the unoptimmized mir
/// bodies are stolen.
pub fn dump_mir_and_borrowck_facts(tcx: TyCtxt) {
    let mut vis = DumpingVisitor {
        tcx,
        target_dir: intermediate_out_dir(tcx, INTERMEDIATE_ARTIFACT_EXT),
    };
    tcx.hir().visit_all_item_likes_in_crate(&mut vis);
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
fn load_body_and_facts(tcx: TyCtxt<'_>, def_id: DefId) -> CachedBody<'_> {
    let paths = local_or_remote_paths(def_id.krate, tcx, INTERMEDIATE_ARTIFACT_EXT);
    for path in &paths {
        let path = path.join(tcx.def_path(def_id).to_filename_friendly_no_crate());
        if let Ok(data) = decode_from_file(tcx, path) {
            return data;
        };
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

    let file = if file.starts_with("lib") {
        std::borrow::Cow::Borrowed(file)
    } else {
        format!("lib{file}").into()
    };

    dir.join(file.as_ref())
}
