#![allow(dead_code)]
extern crate either;
extern crate rustc_hir as hir;
extern crate rustc_middle;
extern crate rustc_span;

use hir::def_id::DefId;
use paralegal_non_rustc_utils::prepare_analyzer_command;
use rustc_errors::FatalError;
use rustc_middle::ty::TyCtxt;

use crate::{
    Callbacks, EXTRA_RUSTC_ARGS, HashSet,
    ann::{db::AutoMarkers, dump_markers},
    desc::{Identifier, ProgramDescription},
    utils::Print,
};
use std::{ffi::OsString, fmt::Display, io::Write, path::PathBuf, sync::atomic::Ordering};
use std::{
    fmt::{Debug, Formatter},
    sync::Once,
};
use std::{
    hash::{Hash, Hasher},
    sync::atomic::AtomicU32,
};

use paralegal_spdg::{
    DefInfo, DisplayPath, EdgeInfo, Endpoint, FileSystemStorable, InstructionInfo, InstructionKind,
    Node, NodeInfo, NodeKind, ParalegalArtifact, SPDG, TypeId,
    traverse::{EdgeSelection, generic_flows_to, generic_influencers},
    utils::{display_list, write_sep},
};

use flowistry_pdg::{CallString, Constant, GlobalLocation};
use itertools::Itertools;
use petgraph::visit::{Control, Data, DfsEvent, EdgeRef, FilterEdge, GraphBase, IntoEdges};
use petgraph::visit::{IntoNeighbors, IntoNodeReferences};
use petgraph::visit::{NodeRef as _, Visitable};
use std::path::Path;

lazy_static::lazy_static! {
    pub static ref CWD_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());
}

/// Run an action `F` in the directory `P`, ensuring that afterwards the
/// original working directory is reestablished *and* also takes a lock so that
/// no two parallel processes try to switch directory simultaneously.
pub fn with_current_directory<
    P: AsRef<std::path::Path>,
    A,
    F: std::panic::UnwindSafe + FnOnce() -> A,
>(
    p: P,
    f: F,
) -> std::io::Result<A> {
    let _guard = CWD_MUTEX.lock().unwrap();
    let current = std::env::current_dir()?;
    std::env::set_current_dir(p)?;
    let res = f();
    std::env::set_current_dir(current)?;
    Ok(res)
}

/// Initialize rustc data structures (e.g. [`Symbol`] works) and run `F`
///
/// Be aware that any [`Symbol`] created in `F` will **not** compare equal to
/// [`Symbol`]s created after `F` and may cause dereference errors.
pub fn use_rustc<A, F: FnOnce() -> A>(f: F) -> A {
    rustc_span::create_session_if_not_set_then(rustc_span::edition::DEFAULT_EDITION, |_| f())
}

/// Crates a basic invocation of `cargo paralegal-flow`, ensuring that the `cargo-paralegal-flow`
/// and `paralegal-flow` executables that were built from this project are (first) in the
/// `PATH`.
pub fn paralegal_flow_command(dir: impl AsRef<Path>) -> std::process::Command {
    let factory = prepare_analyzer_command(Path::new("../..")).unwrap();
    // Force paralegal-flow binary to be built
    let mut cmd = factory.make();
    cmd.current_dir(dir);
    eprintln!("Command is {cmd:?}");
    cmd
}

/// Run paralegal-flow in the current directory, passing the
/// `--dump-serialized-flow-graph` which dumps the [`ProgramDescription`] as
/// JSON.
///
/// The result is suitable for reading with [`PreFrg::from_file_at`]
pub fn run_paralegal_flow_with_flow_graph_dump(dir: impl AsRef<Path>) -> bool {
    run_paralegal_flow_with_flow_graph_dump_and::<_, &str>(dir, [])
}

/// Run paralegal-flow in the current directory, passing the
/// `--dump-serialized-flow-graph` which dumps the [`ProgramDescription`] as
/// JSON.
///
/// The result is suitable for reading with [`PreFrg::from_file_at`]
pub fn run_paralegal_flow_with_flow_graph_dump_and<I, S>(dir: impl AsRef<Path>, extra: I) -> bool
where
    I: IntoIterator<Item = S>,
    S: AsRef<std::ffi::OsStr>,
{
    let dir = dir.as_ref();
    // assert!(
    //     Command::new("cargo")
    //         .arg("clean")
    //         .current_dir(dir)
    //         .status()
    //         .unwrap()
    //         .success()
    // );
    paralegal_flow_command(dir)
        .args(extra)
        .status()
        .unwrap()
        .success()
}

/// A "meta-macro" that should be used to implement a `define_test!` macro in a
/// test suite. The idea is to provide the first two arguments per test-suite and
/// forward the rest to be provided on a per-test basis. For example:
///
/// ```
/// macro_rules! define_test {
///     ($($t:tt)*) => {
///         define_flow_test_template!(TEST_CRATE_ANALYZED, CRATE_DIR, $($t)*);
///     };
/// }
/// ```
///
/// The arguments are as follows:
/// - `$analyze`: a lazy boolean to wait for which indicates that the analysis
///   has finished.
/// - `$crate_name`: The path to the crate that was analyzed
/// - `$name`: The name to use for the test function.
/// - `skip $reason`: Optional. If this is provided the test will be
///   `#[ignore]`d. The `$reason` is mandatory and should explain why this test
///   is skipped and under which conditions it should be reenabled.
/// - `$ctrl`: The name to bind the deserialized SPDG to.
/// - `$ctrl_name`: The entry point for which to retrieve the SPDG, defaults to
///   `$name` if omitted.
/// - `$block`: The test code.
#[macro_export]
macro_rules! define_flow_test_template {
    ($analyze:expr, $crate_name:expr, $name:ident skip $reason:literal : $ctrl:ident, $ctrl_name:ident -> $block:block) => {
        $crate::define_flow_test_template!($analyze, $crate_name, #[ignore = $reason] $name : $ctrl, $ctrl_name -> $block);
    };
    ($analyze:expr, $crate_name:expr, $name:ident $(skip $reason:literal)? : $ctrl:ident -> $block:block) => {
        $crate::define_flow_test_template!($analyze, $crate_name, $name $(skip $reason)?: $ctrl, $name -> $block);
    };
    ($analyze:expr, $crate_name:expr, $(#[$($attr:tt)+])* $name:ident: $ctrl:ident, $ctrl_name:ident -> $block:block) => {
        #[test]
        $(#[$($attr)+])*
        fn $name() {
            assert!(*$analyze);
            $crate::test_utils::use_rustc(|| {
                let graph = $crate::test_utils::PreFrg::from_file_at($crate_name);
                let $ctrl = $crate::test_utils::HasGraph::ctrl(&graph, stringify!($ctrl_name));
                $block
            })
        }
    };
}

/// Configures and builds a reusable dependency environment for inline tests.
///
/// Allows multiple tests in the same session to share compiled stdlib and other
/// dependencies, avoiding redundant recompilation. Uses `Once` internally to
/// ensure dependencies are compiled only once.
///
/// # Examples
///
/// Stdlib only:
/// ```no_run
/// # use paralegal_flow::test_utils::DependencyEnvironmentBuilder;
/// let dep_env = DependencyEnvironmentBuilder::new()
///     .with_stdlib()
///     .build();
/// ```
///
/// With external crates from a Cargo.toml:
/// ```no_run
/// # use paralegal_flow::test_utils::DependencyEnvironmentBuilder;
/// # use std::path::Path;
/// let dep_env = DependencyEnvironmentBuilder::new()
///     .with_manifest(Path::new("tests/stub-tests/Cargo.toml"))
///     .build();
/// ```
pub struct DependencyEnvironmentBuilder {
    include_stdlib: bool,
    manifest_path: Option<std::path::PathBuf>,
    markers: Option<PathBuf>,
    extra_args: Vec<String>,
}

/// Holds compiled dependencies for reuse across multiple inline tests.
///
/// Uses `Once` to ensure one-time compilation per session. Once built,
/// caches `--extern` flags and/or rustc flags needed to link dependencies.
///
/// For manifest-based environments, compiles external crates once and caches
/// the resulting `--extern` flags.
///
/// For stdlib environments, this acts as an explicit marker for tests that
/// intentionally rely on stdlib availability from the embedded rustc sysroot.
///
/// This environment is tied to a specific configuration of dependencies and
/// should be created once per test file (or group of related tests) and then
/// shared across multiple `InlineTestBuilder` instances.
#[derive(Clone)]
pub struct DependencyEnvironment {
    // Lazy-initialized rustc flags (cached after first compilation)
    rustc_flags: Vec<String>,
    // Configuration
    include_stdlib: bool,
    manifest_path: Option<std::path::PathBuf>,
    extra_args: Vec<String>,
    marker_file: Option<PathBuf>,
}

impl DependencyEnvironmentBuilder {
    /// Create a new builder with no dependencies configured.
    pub fn new() -> Self {
        Self {
            include_stdlib: false,
            manifest_path: None,
            markers: None,
            extra_args: vec![],
        }
    }

    /// Include the Rust standard library (std, core, alloc).
    ///
    /// This allows tests to use stdlib types like `Vec`, `TcpStream`, etc.
    pub fn with_stdlib(mut self) -> Self {
        self.include_stdlib = true;
        self
    }

    pub fn with_extra_args<S: ToString>(mut self, args: impl IntoIterator<Item = S>) -> Self {
        self.extra_args
            .extend(args.into_iter().map(|s| s.to_string()));
        self
    }

    /// Add external crates from a Cargo.toml manifest.
    ///
    /// The manifest is compiled and its artifacts are linked using `--extern` flags.
    /// This is useful for tests that need third-party crates like `tokio`.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use paralegal_flow::test_utils::DependencyEnvironmentBuilder;
    /// let _env = DependencyEnvironmentBuilder::new()
    ///     .with_manifest("tests/stub-tests/Cargo.toml")
    ///     .build();
    /// ```
    pub fn with_manifest(mut self, path: impl AsRef<std::path::Path>) -> Self {
        self.manifest_path = Some(path.as_ref().to_path_buf());
        self
    }

    pub fn with_markers(mut self, markers: impl AsRef<Path>) -> Self {
        self.markers = Some(markers.as_ref().to_path_buf());
        self
    }

    /// Build a Cargo project and collect all `--extern name=path` rustc args from
    /// the resulting rlib artifacts for the manifest's direct dependencies only.
    /// Useful for inline tests that need to link against external crates.
    ///
    /// Uses the same rustc that compiled this crate (via `SYSROOT_PATH`) so the
    /// rlib crate hashes are compatible with the embedded `rustc_driver`.
    pub fn collect_extern_args(&self, manifest_path: impl AsRef<std::path::Path>) -> Vec<String> {
        let manifest_path = manifest_path.as_ref();
        let direct_dependencies = direct_dependency_names(manifest_path);
        let mut cmd =
            paralegal_flow_command(manifest_path.canonicalize().unwrap().parent().unwrap());
        cmd.arg("--forward-json");
        cmd.args(&self.extra_args);
        let output = cmd
            .output()
            .expect("cargo build failed while collecting extern args");

        if !output.status.success() {
            let _ = std::io::stdout().write(&output.stdout);
            let _ = std::io::stderr().write(&output.stderr);
            panic!(
                "cargo build for extern arg collection failed with status {}",
                output.status
            );
        }

        let mut args = Vec::new();

        if let Some(parent) = manifest_path.parent() {
            let deps_dir = parent.join("target/paralegal/debug/deps");
            args.push("-L".to_string());
            args.push(format!("dependency={}", deps_dir.display()));
        }
        if self.include_stdlib {
            // Required for the noprelude,nounused: extern qualifier syntax.
            args.push("-Zunstable-options".into());
        }
        for line in String::from_utf8(output.stdout).unwrap().lines() {
            let Ok(msg) = serde_json::from_str::<serde_json::Value>(line) else {
                continue;
            };
            if msg["reason"].as_str() != Some("compiler-artifact") {
                continue;
            }
            let Some(name) = msg["target"]["name"].as_str() else {
                continue;
            };
            let extern_name = name.replace('-', "_");
            // Stdlib crates rebuilt via -Zbuild-std are not listed in any
            // [dependencies] section. Identify them by their manifest_path being
            // under the sysroot's lib/rustlib/src tree.
            let sysroot_src = concat!(env!("SYSROOT_PATH"), "/lib/rustlib/src");
            let is_stdlib_artifact = self.include_stdlib
                && msg["manifest_path"]
                    .as_str()
                    .is_some_and(|p| p.starts_with(sysroot_src));

            if !is_stdlib_artifact && !direct_dependencies.contains(&extern_name) {
                continue;
            }
            let Some(filenames) = msg["filenames"].as_array() else {
                continue;
            };
            for f in filenames {
                let path = f.as_str().unwrap();
                if !path.ends_with(".rlib") && !path.ends_with(".rmeta") {
                    continue;
                }
                // Use noprelude for everything except std itself.
                // noprelude prevents duplicate-prelude conflicts; for std
                // we omit it so that its prelude (Ok, Vec, …) is injected
                // into the inline test's root module automatically.
                let qualifier = if is_stdlib_artifact && extern_name != "std" {
                    "noprelude,nounused:"
                } else {
                    ""
                };
                args.push("--extern".to_string());
                args.push(format!("{qualifier}{extern_name}={path}"));
            }
        }
        args
    }

    /// Build the dependency environment.
    ///
    /// This creates (or caches) compiled artifacts that will be reused
    /// across multiple tests in the same session. Compilation happens lazily
    /// on first use.
    pub fn build(self) -> DependencyEnvironment {
        let manifest_path = self.manifest_path.clone().or_else(|| {
            self.include_stdlib.then(|| {
                use std::fs;
                let temp_dir = std::env::temp_dir();
                let project_name = "paralegal-tests-stdlib-only";
                let project_dir = temp_dir.join(project_name);

                // Create project structure
                fs::create_dir_all(project_dir.join("src")).unwrap();

                // Write Cargo.toml as binary crate
                let cargo_toml = format!(
                    r#"[package]
name = "{}"
version = "0.1.0"
edition = "2021"

[[bin]]
name = "{}"
path = "src/main.rs"

[dependencies]
"#,
                    project_name, project_name
                );
                let manifest_path = project_dir.join("Cargo.toml");
                fs::write(&manifest_path, cargo_toml).unwrap();

                // Write src/main.rs (instead of src/lib.rs)
                fs::write(project_dir.join("src/main.rs"), "fn main() {}").unwrap();
                manifest_path
            })
        });

        let flags = if let Some(manifest) = &manifest_path {
            self.collect_extern_args(manifest)
        } else {
            vec![]
        };

        println!("Collected extern args {flags:?}");

        DependencyEnvironment {
            rustc_flags: flags,
            include_stdlib: self.include_stdlib,
            manifest_path: manifest_path,
            extra_args: self.extra_args,
            marker_file: self.markers,
        }
    }
}

impl Default for DependencyEnvironmentBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl DependencyEnvironment {
    /// Get the rustc flags (including `--extern` arguments) for this dependency environment.
    ///
    /// Initializes (compiles) the environment on first call; subsequent calls
    /// return cached flags. This is suitable for passing directly to
    /// [`InlineTestBuilder::with_rustc_args`].
    pub fn rustc_flags(&self) -> &[String] {
        &self.rustc_flags
    }
}

/// Builder for running test cases against a string of source code.
///
/// Start with [`InlineTestBuilder::new`], compile and run the test case with
/// [`InlineTestBuilder::check`].
#[derive(Clone)]
pub struct InlineTestBuilder {
    ctrl_name: Option<String>,
    input: String,
    extra_args: Vec<String>,
    marker_file: Option<PathBuf>,
    build_config: Option<PathBuf>,
    rustc_args: Vec<String>,
}

#[macro_export]
macro_rules! inline_test {
    ($($t:tt)*) => {
        $crate::test_utils::InlineTestBuilder::new(stringify!($($t)*))
    };
}

static FILE_INDEX: AtomicU32 = AtomicU32::new(0);

impl InlineTestBuilder {
    /// Constructor.
    ///
    /// Note that this test builder does not support specifying dependencies,
    /// including the `paralegal` library. As such use raw annotations like
    /// `#[paralegal_flow::marker(...)]`.
    ///
    /// By default a `main` function is used as the analysis target (even
    /// without an `analyze` annotation). Use
    /// [`InlineTestBuilder::with_entrypoint`] to use a different function.
    pub fn new(input: impl Into<String>) -> Self {
        Self {
            input: input.into(),
            ctrl_name: Some("crate::main".into()),
            extra_args: Default::default(),
            marker_file: None,
            build_config: None,
            rustc_args: Default::default(),
        }
    }

    /// Chose a function as analysis entrypoint. Overwrites any previous choice
    /// without warning.
    pub fn with_entrypoint(&mut self, name: impl Into<String>) -> &mut Self {
        self.ctrl_name = Some(name.into());
        self
    }

    pub fn with_extra_args<S: ToString>(&mut self, args: impl IntoIterator<Item = S>) -> &mut Self {
        self.extra_args
            .extend(args.into_iter().map(|s| s.to_string()));
        self
    }

    pub fn expect_fail_compile(&self) {
        let reached = Once::new();
        let res = self.run(|_| reached.call_once(|| ()));
        assert!(res.is_err(), "the compiler existed successfully");
    }

    pub fn without_entrypoint(&mut self) -> &mut Self {
        self.ctrl_name = None;
        self
    }

    pub fn with_marker_file(&mut self, marker_file: &Path) -> &mut Self {
        self.marker_file = Some(marker_file.to_path_buf());
        self
    }

    pub fn with_build_config(&mut self, config: &Path) -> &mut Self {
        self.build_config = Some(config.to_path_buf());
        self
    }

    pub fn with_rustc_args<S: ToString>(&mut self, args: impl IntoIterator<Item = S>) -> &mut Self {
        self.rustc_args
            .extend(args.into_iter().map(|s| s.to_string()));
        self
    }

    /// Use a pre-built dependency environment for this test.
    ///
    /// This allows multiple tests to share compiled dependencies, avoiding
    /// redundant recompilation. The environment provides rustc flags (like `--extern`)
    /// that are applied automatically to the compilation.
    ///
    /// When the environment includes external crates (from a Cargo.toml manifest),
    /// direct rustc compilation is used. When it only includes stdlib, Cargo-based
    /// compilation is used to ensure proper linking.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use paralegal_flow::test_utils::DependencyEnvironmentBuilder;
    /// # use paralegal_flow::inline_test;
    /// let env = DependencyEnvironmentBuilder::new()
    ///     .with_manifest("tests/stub-tests/Cargo.toml")
    ///     .build();
    ///
    /// inline_test! { /* code */ }
    ///     .with_dependency_environment(&env)
    ///     .check_ctrl(|ctrl| { /* ... */ });
    /// ```
    pub fn with_dependency_environment(&mut self, env: &DependencyEnvironment) -> &mut Self {
        // Add the environment's rustc flags
        let flags = env.rustc_flags();
        if !flags.is_empty() {
            self.rustc_args.extend(flags.iter().cloned());
        }
        self.extra_args.extend(env.extra_args.iter().cloned());
        self.marker_file = env.marker_file.clone();

        self
    }

    /// Legacy compatibility shim.
    ///
    /// Inline tests now always use the embedded rustc path. Standard library
    /// availability is controlled by rustc's sysroot, so this no longer toggles
    /// a Cargo-based test compile mode.
    pub fn with_dependencies(&mut self) -> &mut Self {
        self
    }

    /// Compile the code, select the [`CtrlRef`] corresponding to the configured
    /// entrypoint and hand it to the `check` function which should contain the
    /// test predicate.
    pub fn check_ctrl(&self, check: impl FnOnce(CtrlRef) + Send) {
        self.run(|graph| {
            let cref = graph.ctrl(self.ctrl_name.as_ref().unwrap());
            check(cref);
        })
        .unwrap()
    }

    pub fn run(&self, f: impl FnOnce(PreFrg) + Send) -> Result<(), FatalError> {
        self.run_with_tcx(|_, graph| f(graph))
    }

    pub fn run_with_tcx(
        &self,
        f: impl for<'tcx> FnOnce(TyCtxt<'tcx>, PreFrg) + Send,
    ) -> Result<(), FatalError> {
        use clap::Parser;

        #[derive(clap::Parser)]
        struct TopLevelArgs {
            #[clap(flatten)]
            args: crate::ClapArgs,
        }

        let mut args: Vec<OsString> = vec!["".into()];
        if let Some(e) = &self.ctrl_name {
            args.extend(["--analyze".into(), e.into()])
        }
        if let Some(m) = &self.marker_file {
            args.push("--external-annotations".into());
            args.push(m.into());
        }
        if let Some(c) = &self.build_config {
            args.push("--build-config".into());
            args.push(c.into());
        }
        args.extend(self.extra_args.iter().map(|s| s.into()));

        let args = crate::Args::try_from(TopLevelArgs::parse_from(args).args).unwrap();

        let _ = args.setup_logging();

        paralegal_rustc_utils::test_utils::CompileBuilder::new(&self.input)
            .with_args(EXTRA_RUSTC_ARGS.iter().copied().map(ToOwned::to_owned))
            .with_args(["-Ztrack-diagnostics".to_string()])
            .with_args(self.rustc_args.iter().cloned())
            .compile(move |result| {
                let args: &'static _ = Box::leak(Box::new(args));
                dump_markers(result.tcx);
                let tcx = result.tcx;
                let (pdg, _) = Callbacks::new(args)
                    .run_in_context_without_writing_stats(tcx)
                    .unwrap();
                let graph = PreFrg::from_description(pdg);
                f(tcx, graph)
            })
    }
}

pub trait HasGraph<'g>: Sized + Copy {
    fn graph(self) -> &'g PreFrg;

    fn functions(self, name: impl AsRef<str>) -> Box<dyn Iterator<Item = FnRef<'g>> + 'g> {
        let name = Identifier::new_intern(name.as_ref());
        let graph = self.graph();
        Box::new(
            graph.name_map[&name]
                .as_slice()
                .iter()
                .map(move |&id| FnRef { graph, ident: id }),
        )
    }

    fn has_function(self, name: impl AsRef<str>) -> bool {
        let name = Identifier::new_intern(name.as_ref());
        self.graph().name_map.contains_key(&name)
    }

    fn markers(self) -> HashSet<Identifier> {
        let graph = self.graph();
        graph
            .desc
            .controllers
            .values()
            .flat_map(|c| c.markers.values())
            .flat_map(|b| b.iter().cloned())
            .collect()
    }

    fn marked_types(&self, marker: Identifier) -> Vec<TypeId> {
        self.graph()
            .desc
            .type_info
            .iter()
            .filter_map(|(id, desc)| desc.markers.contains(&marker).then_some(*id))
            .collect()
    }

    /// Use [Self::async_function] for async functions
    fn function(self, name: impl AsRef<str>) -> FnRef<'g> {
        let name = Identifier::new_intern(name.as_ref());
        let id = match self.graph().name_map.get(&name).map(Vec::as_slice) {
            Some([one]) => *one,
            Some([]) | None => panic!("Did not find name {name}",),
            _ => panic!("Found too many function matching name {name}"),
        };
        FnRef {
            graph: self.graph(),
            ident: id,
        }
    }

    fn async_function(self, name: impl AsRef<str>) -> FnRef<'g> {
        self.function(format!("{}_coroutine", name.as_ref()))
    }

    fn info_for(self, id: DefId) -> &'g DefInfo {
        &self.graph().desc.def_info[&id]
    }

    fn ctrl(self, name: &str) -> CtrlRef<'g> {
        let id = self.ctrl_hashed(name);
        CtrlRef {
            graph: self.graph(),
            id,
            ctrl: &self.graph().desc.controllers[&id],
        }
    }

    fn ctrl_hashed(self, name: &str) -> Endpoint {
        let name = name.strip_prefix("crate::").unwrap_or(name);
        let candidates = self
            .graph()
            .desc
            .controllers
            .iter()
            .filter(|(_id, info)| info.name.as_str() == name)
            .map(|(id, _)| *id)
            .collect::<Vec<_>>();
        match candidates.as_slice() {
            [] => panic!(
                "Could not find controller '{name}'. Known controllers are {}",
                Print(|fmt| {
                    write_sep(fmt, ", ", self.graph().desc.controllers.values(), |c, f| {
                        f.write_str(c.name.as_str())
                    })
                })
            ),
            [ctrl] => *ctrl,
            more => panic!("Too many matching controllers, found candidates: {more:?}"),
        }
    }

    fn has_marker(self, marker: &str) -> bool {
        let marker = Identifier::new_intern(marker);
        self.graph()
            .desc
            .type_info
            .values()
            .any(|t| t.markers.contains(&marker))
            || self
                .graph()
                .desc
                .controllers
                .values()
                .any(|c| c.markers.values().any(|m| m.contains(&marker)))
    }
}

#[derive(Debug)]
pub struct PreFrg {
    pub desc: ProgramDescription,
    pub name_map: crate::HashMap<Identifier, Vec<DefId>>,
}

impl<'g> HasGraph<'g> for &'g PreFrg {
    fn graph(self) -> &'g PreFrg {
        self
    }
}

impl PreFrg {
    pub fn display_location(&self, loc: GlobalLocation) -> impl Display + '_ {
        struct DisplayGlobalLoc<'a> {
            loc: GlobalLocation,
            gr: &'a ProgramDescription,
        }

        impl Display for DisplayGlobalLoc<'_> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                write!(
                    f,
                    "{} in {}",
                    self.gr.instruction_info[&self.loc].description,
                    DisplayPath::from(&self.gr.def_info[&self.loc.function].path)
                )
            }
        }

        DisplayGlobalLoc {
            gr: &self.desc,
            loc,
        }
    }

    pub fn from_file_at(dir: &str) -> Self {
        use_rustc(|| {
            let path = Path::new(dir).join(paralegal_non_rustc_utils::ARTIFACT_NAME);
            let artifact = ParalegalArtifact::load(&path).unwrap();
            let desc_path = match artifact.targets.as_slice() {
                [p] => p,
                [] => panic!("Artifact at {} had no target crates", path.display()),
                other => panic!(
                    "Artifact at {} had too many target crates ({})",
                    path.display(),
                    other.len()
                ),
            };
            let desc = ProgramDescription::canonical_read(desc_path).unwrap();
            Self::from_description(desc)
        })
    }

    pub fn from_description(desc: ProgramDescription) -> Self {
        let name_map = desc
            .def_info
            .iter()
            .map(|(def_id, info)| (info.name, *def_id))
            .into_group_map();
        Self { desc, name_map }
    }
}

#[derive(Clone)]
pub struct CtrlRef<'g> {
    graph: &'g PreFrg,
    id: Endpoint,
    ctrl: &'g SPDG,
}

impl Debug for CtrlRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CtrlRef")
            .field("ident", &self.ctrl.name)
            .finish()
    }
}

impl PartialEq for CtrlRef<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<'g> HasGraph<'g> for &CtrlRef<'g> {
    fn graph(self) -> &'g PreFrg {
        self.graph.graph()
    }

    fn markers(self) -> HashSet<Identifier> {
        self.ctrl
            .markers
            .values()
            .flat_map(|b| b.iter().cloned())
            .collect()
    }

    fn has_function(self, name: impl AsRef<str>) -> bool {
        let name = Identifier::new_intern(name.as_ref());
        self.graph().name_map.get(&name).is_some_and(|f| {
            let set = f.iter().cloned().collect::<HashSet<_>>();
            self.ctrl.graph.node_references()
                .any(|n| {
                    let found = matches!(self.graph.desc.instruction_info[&n.1.at.leaf()], InstructionInfo { kind: InstructionKind::FunctionCall(f), .. } if set.contains(&f.id));
                    if found {
                        println!("Found call to {name} in {}", n.1);
                    }
                    found
                })
        })
    }
}

impl<'g> CtrlRef<'g> {
    pub fn return_value(&self) -> NodeRefs<'_> {
        // TODO only include mutable formal parameters?
        let nodes = self.ctrl.return_.to_vec();
        NodeRefs { nodes, graph: self }
    }

    pub fn returns(&self, other: &impl FlowsTo) -> bool {
        other.flows_to_data(&self.return_value())
    }

    pub fn marked(&self, marker: impl Into<Identifier>) -> NodeRefs<'_> {
        let marker = marker.into();
        let marked_types = self
            .graph
            .marked_types(marker)
            .into_iter()
            .collect::<HashSet<_>>();
        NodeRefs {
            nodes: self
                .ctrl
                .markers
                .iter()
                .filter(|(_, markers)| markers.contains(&marker))
                .map(|(n, _)| *n)
                .chain(self.ctrl.type_assigns.iter().filter_map(|(n, types)| {
                    types
                        .0
                        .iter()
                        .any(|t| marked_types.contains(t))
                        .then_some(*n)
                }))
                .collect(),
            graph: self,
        }
    }

    pub fn id(&self) -> Endpoint {
        self.id
    }
    pub fn spdg(&self) -> &'g SPDG {
        self.ctrl
    }

    pub fn call_sites(&'g self, fun: &'g FnRef<'g>) -> Vec<CallStringRef<'g>> {
        let instruction_info = &self.graph.desc.instruction_info;

        let all: HashSet<CallStringRef<'g>> = self
            .ctrl
            .graph
            .edge_weights()
            .map(|v| v.at)
            .chain(self.ctrl.graph.node_weights().map(|info| info.at))
            .filter(|m| {
                instruction_info[&m.leaf()]
                    .kind
                    .as_function_call()
                    .is_some_and(|i| i.id == fun.ident)
            })
            .map(|call_site| CallStringRef {
                ctrl: self,
                call_site,
            })
            .collect();
        Vec::from_iter(all)
    }

    pub fn call_site(&'g self, fun: &'g FnRef<'g>) -> CallStringRef<'g> {
        let mut cs = self.call_sites(fun);
        assert!(
            cs.len() == 1,
            "expected only one call site for {}, found {}",
            fun.info_for(fun.ident).name,
            display_list(cs.iter().map(|c| c.call_site))
        );
        cs.pop().unwrap()
    }

    pub fn types_for(&'g self, target: Node) -> &'g [DefId] {
        self.ctrl
            .type_assigns
            .get(&target)
            .map_or(&[], |t| t.0.as_ref())
    }

    pub fn nodes_for_type(&self, typ: TypeId) -> NodeRefs<'_> {
        NodeRefs {
            graph: self,
            nodes: self
                .ctrl
                .type_assigns
                .iter()
                .filter_map(|(n, types)| types.0.contains(&typ).then_some(*n))
                .collect(),
        }
    }

    pub fn arguments(&'g self) -> NodeRefs<'g> {
        NodeRefs {
            nodes: self.ctrl.arguments.to_vec(),
            graph: self,
        }
    }

    pub fn constants(&'g self) -> impl Iterator<Item = (NodeRef<'g>, Constant)> {
        let spdg = self.spdg();
        spdg.all_sources().filter_map(|node| {
            let info = spdg.node_info(node);
            match info.kind {
                NodeKind::Constant(c) => Some((NodeRef { graph: self, node }, c)),
                _ => None,
            }
        })
    }

    pub fn get_constant(&'g self, constant: Constant) -> Option<NodeRef<'g>> {
        self.constants()
            .find(|&(_, c)| c == constant)
            .map(|(n, _)| n)
    }

    pub fn assert_purity(&self, pure: bool) {
        let auto_markers = AutoMarkers::default();
        let auto = auto_markers.all();
        let auto_set = auto.iter().copied().collect::<HashSet<_>>();

        if pure {
            let mut found_instance = false;
            for (n, ms) in self.ctrl.markers.iter() {
                let found = ms
                    .iter()
                    .copied()
                    .filter(|m| auto_set.contains(m))
                    .collect::<Box<[_]>>();
                if !found.is_empty() {
                    found_instance = true;
                    let info = self.ctrl.node_info(*n);
                    println!(
                        "Found side effects {} for node {}",
                        display_list(found.iter()),
                        info
                    );
                    for at in info.at.iter() {
                        println!("  Reached from {}", self.graph.display_location(at));
                    }
                }
            }
            assert!(!found_instance);
        } else {
            let defined = self.markers();
            let contained = auto
                .iter()
                .filter(|m| defined.contains(m))
                .collect::<Vec<_>>();
            assert!(
                !contained.is_empty(),
                "Expected side effects but found none. Found the following markers: {}",
                display_list(defined.iter())
            );
        }
    }

    pub fn side_effect_nodes(&'g self) -> impl Iterator<Item = NodeRef<'g>> {
        let auto_markers = AutoMarkers::default();
        let auto = auto_markers.all();
        auto.into_iter().flat_map(|m| self.marked(m))
    }
}

impl<'g> HasGraph<'g> for &FnRef<'g> {
    fn graph(self) -> &'g PreFrg {
        self.graph.graph()
    }
}

pub struct FnRef<'g> {
    graph: &'g PreFrg,
    pub ident: DefId,
}

impl<'g> FnRef<'g> {
    fn graph(&self) -> &'g PreFrg {
        self.graph.graph()
    }
}

pub struct CallStringRef<'g> {
    call_site: CallString,
    ctrl: &'g CtrlRef<'g>,
}

impl std::fmt::Debug for CallStringRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CallStringRef")
            .field("call_site", &self.call_site)
            .field("ctrl", &DisplayPath::from(&self.ctrl.ctrl.path))
            .finish()
    }
}

impl Hash for CallStringRef<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.call_site.hash(state)
    }
}

impl PartialEq for CallStringRef<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.call_site.eq(&other.call_site)
    }
}

impl Eq for CallStringRef<'_> {}

impl PartialEq<CallString> for CallStringRef<'_> {
    fn eq(&self, other: &CallString) -> bool {
        self.call_site == *other
    }
}

impl<'g> CallStringRef<'g> {
    pub fn input(&'g self) -> NodeRefs<'g> {
        let graph = &self.ctrl.ctrl.graph;
        // Alternative??
        let mut nodes: Vec<_> = graph
            .node_references()
            .filter(|e| e.weight().at == self.call_site)
            .filter_map(|e| Some((e.weight().is_arg?, e.id())))
            .collect();
        nodes.sort();
        nodes.dedup();
        NodeRefs {
            nodes: nodes.into_iter().map(|t| t.1).collect(),
            graph: self.ctrl,
        }
    }

    pub fn output(&self) -> NodeRefs<'g> {
        let graph = &self.ctrl.ctrl.graph;
        let mut nodes: Vec<_> = graph
            .edge_references()
            .filter(|e| e.weight().at == self.call_site)
            .map(|e| e.target())
            .chain(
                graph
                    .node_references()
                    .filter(|n| n.weight().at == self.call_site)
                    .map(|n| n.id()),
            )
            .collect();
        nodes.sort();
        nodes.dedup();
        NodeRefs {
            nodes,
            graph: self.ctrl,
        }
    }
    pub fn call_site(&self) -> CallString {
        self.call_site
    }
}

impl<'g> HasGraph<'g> for &CallStringRef<'g> {
    fn graph(self) -> &'g PreFrg {
        self.ctrl.graph
    }
}

/// Selecting input or output nodes for a given call site can now return multiple
/// nodes that are independently tracked by the SPDG if we are dealing with an aggregated
/// object, where the fields are tracked independently, or a pointer where the value behind
/// the pointer is tracked separately.
///
/// This type makes it easier to deal with such node collections by allowing you to interrogate
/// flows from and to the collection via [`FlowsTo`]. Make sure to read the documentation on this
/// type's instance of [`FlowsTo`] for the semantics.
pub struct NodeRefs<'g> {
    nodes: Vec<Node>,
    graph: &'g CtrlRef<'g>,
}

impl Debug for NodeRefs<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();
        for &n in &self.nodes {
            let weight = self.graph.ctrl.graph.node_weight(n).unwrap();
            list.entry(&format!("{n:?} {}", weight));
        }
        list.finish()
    }
}

pub struct NodeRefsIter<'g> {
    nodes: std::vec::IntoIter<Node>,
    graph: &'g CtrlRef<'g>,
}

impl<'g> Iterator for NodeRefsIter<'g> {
    type Item = NodeRef<'g>;

    fn next(&mut self) -> Option<Self::Item> {
        self.nodes.next().map(|node| NodeRef {
            node,
            graph: self.graph,
        })
    }
}

impl<'g> IntoIterator for NodeRefs<'g> {
    type Item = NodeRef<'g>;
    type IntoIter = NodeRefsIter<'g>;

    fn into_iter(self) -> Self::IntoIter {
        NodeRefsIter {
            nodes: self.nodes.into_iter(),
            graph: self.graph,
        }
    }
}

impl<'g> FromIterator<NodeRef<'g>> for NodeRefs<'g> {
    fn from_iter<T: IntoIterator<Item = NodeRef<'g>>>(iter: T) -> Self {
        let mut i = iter.into_iter();
        let one = i
            .next()
            .expect("Cannot build node refs from empty iterator");
        Self {
            nodes: [one.node]
                .into_iter()
                .chain(i.map(|n| {
                    assert!(n.graph.id() == one.graph.id());
                    n.node
                }))
                .collect(),
            graph: one.graph,
        }
    }
}

impl<'g> NodeRefs<'g> {
    pub fn nth(&self, i: usize) -> Option<NodeRef<'g>> {
        Some(NodeRef {
            graph: self.graph,
            node: *self.nodes.get(i)?,
        })
    }

    pub fn as_singles(&self) -> impl Iterator<Item = NodeRef<'g>> + '_ {
        let graph = self.graph;
        self.nodes
            .iter()
            .copied()
            .map(|node| NodeRef { node, graph })
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

pub struct NodeRef<'g> {
    node: Node,
    graph: &'g CtrlRef<'g>,
}

impl Debug for NodeRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let weight = self.info();
        f.debug_struct("NodeRef")
            .field("node", &self.node)
            .field("description", &weight.kind)
            .field("at", &weight.at)
            .field("graph", &DisplayPath::from(&self.graph.ctrl.path))
            .finish()
    }
}

impl<'g> HasGraph<'g> for &NodeRef<'g> {
    fn graph(self) -> &'g PreFrg {
        self.graph.graph
    }
}

impl NodeRef<'_> {
    pub fn node(&self) -> Node {
        self.node
    }

    pub fn info(&self) -> &NodeInfo {
        self.graph.ctrl.graph.node_weight(self.node).unwrap()
    }

    pub fn instruction_info(&self) -> &InstructionInfo {
        let g = self.graph();
        &g.desc.instruction_info[&self.info().at.leaf()]
    }
}

impl FlowsTo for NodeRef<'_> {
    fn nodes(&self) -> &[Node] {
        std::slice::from_ref(&self.node)
    }

    fn spdg(&self) -> &SPDG {
        self.graph.ctrl
    }

    fn spdg_ident(&self) -> Identifier {
        self.graph.spdg().name
    }
}

/// If this type is used as an argument to the methods here (both as self or as other) the
/// collection of nodes is interpreted as an "any". E.g. if this is the source, a connection
/// from just one of the nodes to the target need exist. Conversely if used as a target only
/// one of the nodes need be reached from the source.
impl FlowsTo for NodeRefs<'_> {
    fn nodes(&self) -> &[Node] {
        self.nodes.as_slice()
    }

    fn spdg(&self) -> &SPDG {
        self.graph.ctrl
    }

    fn spdg_ident(&self) -> Identifier {
        self.graph.spdg().name
    }
}

/// Lets us test if two graph nodes are connected. For convenience multiple nodes
/// can be tested at a time via `NodeRefs`.
pub trait FlowsTo {
    fn nodes(&self) -> &[Node];
    fn spdg(&self) -> &SPDG;
    fn spdg_ident(&self) -> Identifier;

    fn overlaps(&self, other: &impl FlowsTo) -> bool {
        self.nodes().iter().any(|n| other.nodes().contains(n))
    }

    /// Is there a path consisting of only data flow edges connecting `self` to `other`
    fn flows_to_data(&self, other: &impl FlowsTo) -> bool {
        flows_to_impl(self, other, EdgeSelection::Data)
    }

    /// Is there a path consisting of only control flow edges connecting `self` to `other`
    fn flows_to_ctrl(&self, other: &impl FlowsTo) -> bool {
        flows_to_impl(self, other, EdgeSelection::Control)
    }

    /// Is there a path connecting `self` to `other`
    fn flows_to_any(&self, other: &impl FlowsTo) -> bool {
        flows_to_impl(self, other, EdgeSelection::Both)
    }

    /// Is there a control flow edge connecting `self` to `other`
    fn is_neighbor_ctrl(&self, other: &impl FlowsTo) -> bool {
        is_neighbor_impl(self, other, EdgeSelection::Control)
    }

    /// Is there a data flow edge connecting `self` to `other`
    fn is_neighbor_data(&self, other: &impl FlowsTo) -> bool {
        is_neighbor_impl(self, other, EdgeSelection::Data)
    }

    /// Is there any type of edge connecting `self` to `other`
    fn is_neighbor_any(&self, other: &impl FlowsTo) -> bool {
        is_neighbor_impl(self, other, EdgeSelection::Both)
    }

    /// A special case of a path between `self` and `other`.
    /// All edges are data, except the last one. This is meant to convey
    /// a "direct" control flow influence.
    fn influences_ctrl(&self, other: &impl FlowsTo) -> bool {
        influences_ctrl_impl(self, other, EdgeSelection::Data)
    }

    /// A special case of a path between `self` and `other`.
    /// All edges are data, except the last one. This is meant to convey
    /// a control flow influence, though it might be indirect (a farther out
    /// `if` for instance).
    fn influences_next_control(&self, other: &impl FlowsTo) -> bool {
        influences_ctrl_impl(self, other, EdgeSelection::Data)
    }

    /// Does every data path from `self` to `target` pass through one of `checkpoint`.
    fn always_happens_before_data(&self, checkpoint: &impl FlowsTo, target: &impl FlowsTo) -> bool {
        always_happens_before_impl(self, checkpoint, target, EdgeSelection::Data)
    }

    /// Does every control flow path from `self` to `target` pass through one of `checkpoint`.
    fn always_happens_before_ctrl(&self, checkpoint: &impl FlowsTo, target: &impl FlowsTo) -> bool {
        always_happens_before_impl(self, checkpoint, target, EdgeSelection::Control)
    }

    /// Does every path from `self` to `target` pass through one of `checkpoint`.
    fn always_happens_before_any(&self, checkpoint: &impl FlowsTo, target: &impl FlowsTo) -> bool {
        always_happens_before_impl(self, checkpoint, target, EdgeSelection::Both)
    }

    /// Is there no data flow path from `self` to `target` that crosses through `checkpoint`
    fn never_happens_before_data(&self, checkpoint: &impl FlowsTo, target: &impl FlowsTo) -> bool {
        never_happens_before(self, checkpoint, target, EdgeSelection::Data)
    }

    /// Is there no control flow path from `self` to `target` that crosses through `checkpoint`
    fn never_happens_before_ctrl(&self, checkpoint: &impl FlowsTo, target: &impl FlowsTo) -> bool {
        never_happens_before(self, checkpoint, target, EdgeSelection::Control)
    }

    /// Is there no path from `self` to `target` that crosses through `checkpoint`
    fn never_happens_before_any(&self, checkpoint: &impl FlowsTo, target: &impl FlowsTo) -> bool {
        never_happens_before(self, checkpoint, target, EdgeSelection::Both)
    }

    /// There are no outgoing connections from this (set of) node(s)
    fn is_terminal(&self) -> bool {
        !self
            .nodes()
            .iter()
            .copied()
            .any(|n| self.spdg().graph.neighbors(n).next().is_some())
    }
}

fn influences_ctrl_impl(
    slf: &(impl FlowsTo + ?Sized),
    other: &impl FlowsTo,
    edge_selection: EdgeSelection,
) -> bool {
    if slf.spdg_ident() != other.spdg_ident() {
        return false;
    }

    let ctrl_influencing = generic_influencers(
        &slf.spdg().graph,
        other.nodes().iter().copied(),
        EdgeSelection::Control,
    );

    generic_flows_to(
        slf.nodes().iter().copied(),
        edge_selection,
        slf.spdg(),
        dbg!(ctrl_influencing),
    )
    .is_some()
}

fn is_neighbor_impl(
    slf: &(impl FlowsTo + ?Sized),
    other: &impl FlowsTo,
    edge_selection: EdgeSelection,
) -> bool {
    if slf.spdg_ident() != other.spdg_ident() {
        return false;
    }
    let targets = other.nodes().iter().copied().collect::<HashSet<_>>();
    if slf.nodes().is_empty() {
        return false;
    }
    slf.nodes().iter().any(|&n| {
        targets.contains(&n)
            || slf
                .spdg()
                .graph
                .edges(n)
                .filter(|e| match edge_selection {
                    EdgeSelection::Data => e.weight().is_data(),
                    EdgeSelection::Control => e.weight().is_control(),
                    EdgeSelection::Both => true,
                })
                .any(|e| targets.contains(&e.target()))
    })
}

fn flows_to_impl(
    slf: &(impl FlowsTo + ?Sized),
    other: &impl FlowsTo,
    edge_selection: EdgeSelection,
) -> bool {
    if slf.spdg_ident() != other.spdg_ident() {
        return false;
    }
    generic_flows_to(
        slf.nodes().iter().copied(),
        edge_selection,
        slf.spdg(),
        other.nodes().iter().copied(),
    )
    .is_some()
}

fn always_happens_before_impl(
    src: &(impl FlowsTo + ?Sized),
    checkpoint: &impl FlowsTo,
    target: &impl FlowsTo,
    edge_selection: EdgeSelection,
) -> bool {
    if src.spdg_ident() != target.spdg_ident() {
        return true;
    }

    let spdg = src.spdg();

    happens_before_impl(
        src.nodes(),
        checkpoint.nodes(),
        target.nodes(),
        edge_selection,
        &spdg.graph,
    )
}

fn never_happens_before(
    src: &(impl FlowsTo + ?Sized),
    checkpoint: &impl FlowsTo,
    target: &impl FlowsTo,
    edge_selection: EdgeSelection,
) -> bool {
    if src.spdg_ident() != target.spdg_ident() || checkpoint.spdg_ident() != target.spdg_ident() {
        return true;
    }

    let g = &edge_selection.filter_graph(&src.spdg().graph);

    fn reachable<G: Visitable + IntoNeighbors + GraphBase<NodeId = Node>>(
        g: G,
        start: &[Node],
        end: &[Node],
    ) -> bool {
        let result = petgraph::visit::depth_first_search(g, start.iter().copied(), |ev| match ev {
            DfsEvent::Discover(n, _) if end.contains(&n) => Control::Break(()),
            _ => Control::Continue,
        });
        matches!(result, Control::Break(()))
    }

    !checkpoint
        .nodes()
        .iter()
        .copied()
        .any(|n| reachable(g, src.nodes(), &[n]) && reachable(g, &[n], target.nodes()))
}

fn happens_before_impl<G>(
    from: &[Node],
    via: &[Node],
    to: &[Node],
    edge_selection: EdgeSelection,
    graph: G,
) -> bool
where
    G: Visitable + IntoEdges + GraphBase<NodeId = Node> + Data<EdgeWeight = EdgeInfo>,
    fn(G::EdgeRef) -> bool: FilterEdge<G::EdgeRef>,
{
    let graph = edge_selection.filter_graph(graph);

    let result =
        petgraph::visit::depth_first_search(&graph, from.iter().cloned(), |event| match event {
            DfsEvent::Discover(n, _) if via.contains(&n) => Control::Prune,
            DfsEvent::Discover(n, _) if to.contains(&n) => Control::Break(()),
            _ => Control::Continue,
        });

    !matches!(result, Control::Break(()))
}

fn direct_dependency_names(manifest_path: &std::path::Path) -> std::collections::HashSet<String> {
    let manifest = std::fs::read_to_string(manifest_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", manifest_path.display()));
    let value: toml::Value = toml::from_str(&manifest)
        .unwrap_or_else(|err| panic!("failed to parse {}: {err}", manifest_path.display()));

    let mut names = std::collections::HashSet::new();
    for section in ["dependencies", "dev-dependencies", "build-dependencies"] {
        let Some(table) = value.get(section).and_then(toml::Value::as_table) else {
            continue;
        };
        for (dep_name, dep_value) in table {
            let package_name = dep_value
                .as_table()
                .and_then(|t| t.get("package"))
                .and_then(toml::Value::as_str)
                .unwrap_or(dep_name)
                .replace('-', "_");
            names.insert(package_name);
        }
    }
    names
}
