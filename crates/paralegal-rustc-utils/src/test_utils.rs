//! Running rustc and Flowistry in tests.

use std::{
    fmt::Debug,
    fs,
    hash::Hash,
    io, panic,
    path::Path,
    process::Command,
    sync::{Arc, LazyLock},
};

use anyhow::Result;
use log::debug;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_borrowck::consumers::{get_bodies_with_borrowck_facts, BodyWithBorrowckFacts};
use rustc_data_structures::fx::{FxHashMap as HashMap, FxHashSet as HashSet};
use rustc_errors::FatalError;
use rustc_hir::{def_id::LocalDefId, BodyId, ItemKind};
use rustc_interface::interface;
use rustc_middle::{
    mir::{Body, HasLocalDecls, Local, Place, PlaceTy},
    ty::TyCtxt,
};
use rustc_span::source_map::FileLoader;

use crate::{cache::Cache, BodyExt, PlaceExt};

pub struct StringLoader(pub String);
impl FileLoader for StringLoader {
    fn file_exists(&self, _: &Path) -> bool {
        true
    }

    fn read_file(&self, _: &Path) -> io::Result<String> {
        Ok(self.0.clone())
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        Ok(fs::read(path)?.into())
    }

    fn current_directory(&self) -> io::Result<std::path::PathBuf> {
        std::env::current_dir()
    }
}

static SYSROOT: LazyLock<String> = LazyLock::new(|| {
    let rustc_output = Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap()
        .stdout;
    String::from_utf8(rustc_output).unwrap().trim().to_owned()
});

pub const DUMMY_MOD_NAME: &str = "dummy";
pub const DUMMY_FILE_NAME: &str = "dummy.rs";

/// Programmatically build a rustc compilation session
pub struct CompileBuilder {
    input: String,
    arguments: Vec<String>,
}

impl CompileBuilder {
    /// Initialize a compilation from this string of source code.
    pub fn new(input: impl Into<String>) -> Self {
        Self {
            input: input.into(),
            arguments: vec![],
        }
    }

    /// Append additional rustc arguments
    pub fn with_args(&mut self, args: impl IntoIterator<Item = String>) -> &mut Self {
        self.arguments.extend(args);
        self
    }

    pub fn compile(
        &self,
        f: impl for<'tcx> FnOnce(CompileResult<'tcx>) + Send,
    ) -> Result<(), FatalError> {
        let temp_dir = std::env::temp_dir();
        let random = rand::random::<u64>() / 0x100_000_000_u64;
        let crate_name = format!("crate{random:x}");
        let args = [
            "rustc",
            &crate_name,
            "--crate-type",
            "lib",
            "--edition=2021",
            "-Zidentify-regions",
            "-Zmir-opt-level=0",
            "-Zmaximal-hir-to-mir-coverage",
            "-Ztrack-diagnostics",
            "--allow",
            "warnings",
            "--sysroot",
            &*SYSROOT,
            "--out-dir",
            &format!("{}", temp_dir.display()),
        ]
        .into_iter()
        .map(|s| s.to_owned())
        .chain(self.arguments.iter().cloned())
        .collect::<Box<_>>();

        let mut callbacks = TestCallbacks {
            callback: Some(move |tcx: TyCtxt<'_>| f(CompileResult { crate_name, tcx })),
            input: Some(self.input.clone()),
        };

        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut callbacks))
    }

    pub fn expect_compile(&self, f: impl for<'tcx> FnOnce(CompileResult<'tcx>) + Send) {
        self.compile(f).unwrap();
    }
}

pub fn compile_body(
    input: &str,
    f: impl for<'tcx> FnOnce(TyCtxt<'tcx>, BodyId, &'tcx BodyWithBorrowckFacts<'tcx>) + Send,
) {
    CompileBuilder::new(input).expect_compile(|res| {
        let (body_id, body_with_facts) = res.as_body();
        f(res.tcx, body_id, body_with_facts);
    })
}
thread_local! {
    static BODY_CACHE: Cache<LocalDefId, BodyWithBorrowckFacts<'static>> = Cache::default();
}

pub struct CompileResult<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub crate_name: String,
}

impl<'tcx> CompileResult<'tcx> {
    pub fn as_body(&self) -> (BodyId, &'tcx BodyWithBorrowckFacts<'tcx>) {
        let tcx = self.tcx;
        let body_id = tcx
            .hir_crate_items(())
            .definitions()
            .filter_map(|id| match tcx.hir_expect_item(id).kind {
                ItemKind::Fn { body, .. } => Some(body),
                _ => None,
            })
            .next()
            .unwrap();

        let def_id = tcx.hir_body_owner_def_id(body_id);
        let body_with_facts = BODY_CACHE.with(|cache| {
            let val = cache.get(&def_id, move |_| {
                let mut bodies = get_bodies_with_borrowck_facts(
                    tcx,
                    def_id,
                    rustc_borrowck::consumers::ConsumerOptions::PoloniusInputFacts,
                );
                assert_eq!(bodies.len(), 1);
                let body = bodies.drain().next().unwrap().1;
                unsafe { std::mem::transmute::<_, BodyWithBorrowckFacts<'static>>(body) }
            });
            unsafe { std::mem::transmute::<&_, &'tcx BodyWithBorrowckFacts<'tcx>>(val) }
        });
        debug!("{}", body_with_facts.body.to_string(tcx).unwrap());
        (body_id, body_with_facts)
    }
}

struct TestCallbacks<Cb> {
    callback: Option<Cb>,
    input: Option<String>,
}

impl<Cb> rustc_driver::Callbacks for TestCallbacks<Cb>
where
    Cb: FnOnce(TyCtxt<'_>),
{
    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let callback = self.callback.take().unwrap();
        callback(tcx);
        rustc_driver::Compilation::Stop
    }

    fn config(&mut self, config: &mut interface::Config) {
        config.file_loader = Some(Box::new(StringLoader(
            self.input.take().expect("cannot take input twice"),
        )) as Box<_>)
    }
}

pub struct Placer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    local_map: HashMap<String, Local>,
}

impl<'a, 'tcx> Placer<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>) -> Self {
        let local_map = body.debug_info_name_map();
        Placer {
            tcx,
            body,
            local_map,
        }
    }

    pub fn local(&self, name: &str) -> PlaceBuilder<'a, 'tcx> {
        PlaceBuilder {
            place: Place::from_local(self.local_map[name], self.tcx),
            body: self.body,
            tcx: self.tcx,
        }
    }
}

#[derive(Copy, Clone)]
pub struct PlaceBuilder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    place: Place<'tcx>,
}

impl<'tcx> PlaceBuilder<'_, 'tcx> {
    pub fn field(mut self, i: usize) -> Self {
        let f = FieldIdx::from_usize(i);
        let ty = self.place.ty(self.body.local_decls(), self.tcx);
        let ty = PlaceTy::field_ty(self.tcx, ty.ty, ty.variant_index, f);
        self.place = self.tcx.mk_place_field(self.place, f, ty);
        self
    }

    pub fn deref(mut self) -> Self {
        self.place = self.tcx.mk_place_deref(self.place);
        self
    }

    pub fn downcast(mut self, i: usize) -> Self {
        let ty = self.place.ty(self.body.local_decls(), self.tcx).ty;
        let adt_def = ty.ty_adt_def().unwrap();
        let v = VariantIdx::from_usize(i);
        self.place = self.tcx.mk_place_downcast(self.place, adt_def, v);
        self
    }

    pub fn index(mut self, i: usize) -> Self {
        self.place = self.tcx.mk_place_index(self.place, Local::from_usize(i));
        self
    }

    pub fn mk(self) -> Place<'tcx> {
        self.place
    }
}

pub fn compare_sets<T: PartialEq + Eq + Clone + Hash + Debug>(
    expected: impl IntoIterator<Item = T>,
    actual: impl IntoIterator<Item = T>,
) {
    let expected = expected.into_iter().collect::<HashSet<_>>();
    let actual = actual.into_iter().collect::<HashSet<_>>();

    let missing = &expected - &actual;
    let extra = &actual - &expected;

    let check = |s: HashSet<T>, message: &str| {
        if s.len() > 0 {
            println!(
                "Expected:\n{}",
                textwrap::indent(&format!("{expected:#?}"), "  ")
            );
            println!(
                "Actual:\n{}",
                textwrap::indent(&format!("{actual:#?}"), "  ")
            );
            panic!(
                "{message} ranges:\n{}",
                textwrap::indent(&format!("{s:#?}"), "  ")
            );
        }
    };

    check(missing, "Result did NOT have EXPECTED");
    check(extra, "Result DID have UNEXPECTED");
}
