#![allow(dead_code)]
extern crate either;
extern crate rustc_hir as hir;
extern crate rustc_middle;
extern crate rustc_span;
use crate::{
    desc::{Identifier, ProgramDescription},
    ir::{CallOnlyFlow},
    serializers::{Bodies, InstructionProxy},
    utils::outfile_pls,
    HashSet, Symbol,
};

use paralegal_spdg::{rustc_portable::DefId, DefInfo, Node};
use rustc_middle::mir;

use either::Either;

use crate::pdg::{CallString, GlobalLocation, LocationOrStart};
use itertools::Itertools;
use std::borrow::Cow;
use std::io::prelude::*;
use std::path::Path;
use petgraph::visit::EdgeRef;
use crate::utils::CallStringExt;

lazy_static! {
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
    rustc_span::create_default_session_if_not_set_then(|_| f())
}

/// Run paralegal-flow in the current directory, passing the
/// `--dump-serialized-non-transitive-graph` flag, which dumps a
/// [`CallOnlyFlow`](crate::ir::flows::CallOnlyFlow) for each controller.
///
/// The result is suitable for reading with
/// [`read_non_transitive_graph_and_body`](crate::dbg::read_non_transitive_graph_and_body).
pub fn run_paralegal_flow_with_graph_dump(dir: impl AsRef<Path>) -> bool {
    run_paralegal_flow_with_graph_dump_and::<_, &str>(dir, [])
}

/// Crates a basic invocation of `cargo paralegal-flow`, ensuring that the `cargo-paralegal-flow`
/// and `paralegal-flow` executables that were built from this project are (first) in the
/// `PATH`.
pub fn paralegal_flow_command(dir: impl AsRef<Path>) -> std::process::Command {
    let path = std::env::var("PATH").unwrap_or_else(|_| Default::default());
    let cargo_paralegal_flow_path = Path::new("../../target/debug/cargo-paralegal-flow")
        .canonicalize()
        .unwrap();
    let mut new_path = std::ffi::OsString::with_capacity(
        path.len() + cargo_paralegal_flow_path.as_os_str().len() + 1,
    );
    // We then append the parent (e.g. its directory) to the search path. That
    // directory (we presume) contains both `paralegal-flow` and `cargo-paralegal-flow`.
    new_path.push(cargo_paralegal_flow_path.parent().unwrap_or_else(|| {
        panic!(
            "cargo-paralegal-flow path {} had no parent",
            cargo_paralegal_flow_path.display()
        )
    }));
    new_path.push(":");
    new_path.push(path);
    let mut cmd = std::process::Command::new(cargo_paralegal_flow_path);
    cmd.arg("paralegal-flow")
        .env("PATH", new_path)
        .current_dir(dir);
    eprintln!("Command is {cmd:?}");
    cmd
}

/// Run paralegal-flow in the current directory, passing the
/// `--dump-serialized-non-transitive-graph` flag, which dumps a
/// [`CallOnlyFlow`](crate::ir::flows::CallOnlyFlow) for each controller.
///
/// The result is suitable for reading with
/// [`read_non_transitive_graph_and_body`](crate::dbg::read_non_transitive_graph_and_body).
///
/// Allows for additional arguments to be passed to paralegal-flow
pub fn run_paralegal_flow_with_graph_dump_and<I, S>(dir: impl AsRef<Path>, extra: I) -> bool
where
    I: IntoIterator<Item = S>,
    S: AsRef<std::ffi::OsStr>,
{
    paralegal_flow_command(dir)
        .args([
            "--abort-after-analysis",
            "--dump",
            "serialized-non-transitive-graph",
        ])
        .args(extra)
        .status()
        .unwrap()
        .success()
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
    paralegal_flow_command(dir)
        .args(["--abort-after-analysis", "--dump", "serialized-flow-graph"])
        .args(extra)
        .status()
        .unwrap()
        .success()
}

/// Define a test that is skipped. This can be used to temporarily disable the
/// test. A message can be passed after the test name explaining why it was
/// skipped and the message will be printed when the test is skipped.
///
/// Everything but the first ident and the message are ignored, so the idea is
/// that whatever `define_test` macro you're using and whatever format that
/// macro imposes this should still serve as a drop-in replacement so that you
/// can later remove the `_skip` part and have your test back immediately.
#[macro_export]
macro_rules! define_test_skip {
    ($name:ident $message:literal $($ignored:tt)*) => {
        #[test]
        fn $name() {
            eprintln!(concat!("Skipping test ", stringify!($name), " ", $message));
        }
    };
    ($name:ident $($ignored:tt)*) => {
        define_test_skip!($name "" $($ignored)*);
    };
}

pub const CLEAN_TEMPORARIES: bool = true;

/// A base template for tests that use the [G] representation.
///
/// This takes care of cleaning up the `.ntgb.json` files that are created for
/// the tests. This is to ensure that tests cannot run on old versions of the
/// output. Files are only removed if the test runs successfully.
///
/// Individual test files usually define a convenience macro that passes a
/// test-file-global `analyze` and `crate_dir`.
#[macro_export]
macro_rules! define_G_test_template {
    ($analyze:expr, $crate_dir:expr, $name:ident : $graph:ident -> $block:block) => {
        #[test]
        fn $name() {
            assert!(*$analyze);
            use_rustc(|| {
                let $graph =
                    with_current_directory($crate_dir, || G::from_file(Symbol::intern(stringify!($name)))).unwrap();
                $block
                if CLEAN_TEMPORARIES {
                    let _guard = CWD_MUTEX.lock();
                    let mut p : std::path::PathBuf = $crate_dir.into();
                    p.push(concat!(stringify!($name), ".ntgb.json"));
                    std::fs::remove_file(p).unwrap()
                }
            });
        }
    };
}

#[macro_export]
macro_rules! define_flow_test_template {
    ($analyze:expr, $crate_name:expr, $name:ident: $ctrl:ident, $ctrl_name:ident -> $block:block) => {
        #[test]
        fn $name() {
            assert!(*$analyze);
            use_rustc(|| {
                let graph = PreFrg::from_file_at($crate_name);
                let $ctrl = graph.ctrl(stringify!($ctrl_name));
                $block
            })
        }
    };
}

pub fn run_forge(file: &str) -> bool {
    std::process::Command::new("racket")
        .arg(file)
        .stdout(std::process::Stdio::piped())
        .status()
        .unwrap()
        .success()
}


/// A deserialized version of [`CallOnlyFlow`](crate::ir::flows::CallOnlyFlow)
pub struct G {
    pub graph: CallOnlyFlow,
    pub body: Bodies,
    pub ctrl_name: Identifier,
}

pub trait GetCallSites {
    fn get_call_sites(self, g: &CallOnlyFlow) -> HashSet<CallString>;
}

impl GetCallSites for GlobalLocation {
    fn get_call_sites(self, g: &CallOnlyFlow) -> HashSet<CallString> {
        g.all_locations_iter()
            .filter(move |l| l.leaf() == self)
            .copied()
            .collect()
    }
}

impl GetCallSites for CallString {
    fn get_call_sites(self, _: &CallOnlyFlow) -> HashSet<CallString> {
        [self].into_iter().collect()
    }
}

pub trait MatchCallSite {
    fn match_(self, call_site: CallString) -> bool;
}

impl MatchCallSite for GlobalLocation {
    fn match_(self, call_site: CallString) -> bool {
        self == call_site.leaf()
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum EdgeSelection {
    Data,
    Control,
    Both,
}

impl EdgeSelection {
    fn use_control(self) -> bool {
        matches!(self, EdgeSelection::Control | EdgeSelection::Both)
    }
    fn use_data(self) -> bool {
        matches!(self, EdgeSelection::Data | EdgeSelection::Both)
    }
}

impl G {
    /// Direct predecessor nodes of `n`
    fn predecessors(&self, n: CallString) -> impl Iterator<Item = CallString> + '_ {
        self.predecessors_configurable(n, EdgeSelection::Both)
    }

    pub fn connects_none_configurable<From: MatchCallSite + Copy>(
        &self,
        n: From,
        dir: EdgeSelection,
    ) -> bool {
        self.graph.location_dependencies.iter().all(|(&c, deps)| {
            let iter_all_dep_sets = ||
                dir
                    .use_data()
                    .then_some(deps.input_deps.iter())
                    .into_iter()
                    .flatten()
                    .chain(
                        dir.use_control()
                            .then_some([&deps.ctrl_deps].into_iter())
                            .into_iter()
                            .flatten(),
                    );
            (!n.match_(c)
                || iter_all_dep_sets()
                    .all(|d| d.is_empty()))
                && iter_all_dep_sets()
                    .flatten()
                    .copied()
                    .all(|d| !n.match_(d))
        })
    }

    pub fn connects_none<From: MatchCallSite + Copy>(&self, n: From) -> bool {
        self.connects_none_configurable(n, EdgeSelection::Both)
    }

    fn predecessors_configurable(
        &self,
        n: CallString,
        con_ty: EdgeSelection,
    ) -> impl Iterator<Item = CallString> + '_ {
        self.graph
            .location_dependencies
            .get(&n)
            .into_iter()
            .flat_map(move |deps| {
                con_ty
                    .use_control()
                    .then(|| std::iter::once(&deps.ctrl_deps))
                    .into_iter()
                    .flatten()
                    .chain(
                        con_ty
                            .use_data()
                            .then(|| deps.input_deps.iter())
                            .into_iter()
                            .flatten(),
                    )
                    .flatten()
            })
            .copied()
    }
    pub fn connects<From: MatchCallSite + Copy, To: GetCallSites>(&self, from: From, to: To) -> bool {
        self.connects_configurable(from, to, EdgeSelection::Both)
    }

    pub fn connects_data<From: MatchCallSite + Copy, To: GetCallSites>(
        &self,
        from: From,
        to: To,
    ) -> bool {
        self.connects_configurable(from, to, EdgeSelection::Data)
    }

    pub fn connects_ctrl<From: MatchCallSite + Copy, To: GetCallSites>(
        &self,
        from: From,
        to: To,
    ) -> bool {
        self.connects_configurable(from, to, EdgeSelection::Control)
    }

    /// Is there any path (using directed edges) from `from` to `to`.
    pub fn connects_configurable<From: MatchCallSite + Copy, To: GetCallSites>(
        &self,
        from: From,
        to: To,
        con_ty: EdgeSelection,
    ) -> bool {
        let mut queue = to
            .get_call_sites(&self.graph)
            .into_iter()
            .collect::<Vec<_>>();
        let mut seen = HashSet::new();
        while let Some(n) = queue.pop() {
            if seen.contains(&n) {
                continue;
            } else {
                seen.insert(n);
            }
            for next in self.predecessors_configurable(n, con_ty) {
                if from.match_(next) {
                    return true;
                }
                queue.push(next);
            }
        }
        false
    }

    /// Is there an edge between `from` and `to`. Equivalent to testing if
    /// `from` is in `g.predecessors(to)`.
    pub fn connects_direct_data<From: MatchCallSite + Copy, To: GetCallSites>(
        &self,
        from: From,
        to: To,
    ) -> bool {
        self.connects_direct_configurable(from, to, EdgeSelection::Data)
    }

    pub fn connects_direct<From: MatchCallSite + Copy, To: GetCallSites>(
        &self,
        from: From,
        to: To,
    ) -> bool {
        self.connects_direct_configurable(from, to, EdgeSelection::Both)
    }

    pub fn connects_direct_ctrl<From: MatchCallSite + Copy, To: GetCallSites>(
        &self,
        from: From,
        to: To,
    ) -> bool {
        self.connects_direct_configurable(from, to, EdgeSelection::Control)
    }

    fn connects_direct_configurable<From: MatchCallSite + Copy, To: GetCallSites>(
        &self,
        from: From,
        to: To,
        typ: EdgeSelection,
    ) -> bool {
        for to in to.get_call_sites(&self.graph).iter().copied() {
            if self
                .predecessors_configurable(to, typ)
                .any(|l| from.match_(l))
            {
                return true;
            }
        }
        false
    }

    pub fn returns_direct<From: MatchCallSite + Copy>(&self, from: From) -> bool {
        self.graph
            .return_dependencies
            .iter()
            .copied()
            .any(|d| from.match_(d))
    }

    pub fn returns<From: MatchCallSite + Copy>(&self, from: From) -> bool {
        self.returns_direct(from)
            || self
                .graph
                .return_dependencies
                .iter()
                .any(|&r| self.connects(from, r))
    }

    /// Return all call sites for functions with names matching `pattern`.
    pub fn function_calls(&self, pattern: &str) -> HashSet<GlobalLocation> {
        self.body
            .0
            .iter()
            .flat_map(|(bid, body)| {
                body.1
                     .0
                    .iter()
                    .filter(|s| s.contents.contains(pattern))
                    .map(|s| GlobalLocation {
                        function: bid.expect_local(),
                        location: LocationOrStart::Location(s.location),
                    })
            })
            .collect()
    }

    /// Like `function_calls` but requires that only one such call is found.
    pub fn function_call(&self, pattern: &str) -> GlobalLocation {
        let v = self.function_calls(pattern);
        assert!(
            v.len() == 1,
            "function '{pattern}' should only occur once in {v:?} (found {})",
            v.len()
        );
        v.into_iter().next().unwrap()
    }

    /// Deserialize from a `.ntgb.json` file for the controller named `s`
    pub fn from_file(s: Symbol) -> Self {
        let (graph, body) = crate::dbg::read_non_transitive_graph_and_body(
            std::fs::File::open(format!("{}.ntgb.json", s.as_str())).unwrap(),
        );
        Self {
            graph,
            body,
            ctrl_name: Identifier::new(s),
        }
    }
    pub fn ctrl(&self) -> DefId {
        *self
            .body
            .0
            .iter()
            .find_map(|(id, (name, _))| (*name == self.ctrl_name).then_some(id))
            .unwrap()
    }
    /// Get the `n`th argument for this `bid` body.
    pub fn argument(&self, bid: DefId, n: usize) -> mir::Location {
        let body = &self.body.0[&bid];
        body.1
             .0
            .iter()
            .find(|InstructionProxy { contents, .. }| contents == format!("Argument _{n}").as_str())
            .unwrap_or_else(|| panic!("Argument {n} not found in {:?}", body))
            .location
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

    fn function(self, name: impl AsRef<str>) -> FnRef<'g> {
        let name = Identifier::new_intern(name.as_ref());
        let id = match self.graph().name_map[&name].as_slice() {
            [one] => *one,
            [] => panic!("Did not find name {name}"),
            _ => panic!("Found too many function matching name {name}"),
        };
        FnRef {
            graph: self.graph(),
            ident: id,
        }
    }

    fn info_for(self, id: DefId) -> &'g DefInfo {
        &self.graph().desc.def_info[&id]
    }

    fn ctrl(self, name: &str) -> CtrlRef<'g> {
        let ident = Identifier::new_intern(name);
        CtrlRef {
            graph: self.graph(),
            ident,
            ctrl: &self.graph().desc.controllers[&self.ctrl_hashed(name)],
        }
    }

    fn ctrl_hashed(self, name: &str) -> DefId {
        match self.graph().name_map[&Identifier::new_intern(name)].as_slice() {
            [] => panic!("Could not find controller '{name}'"),
            [ctrl] => *ctrl,
            more => panic!("Too many matching controllers, found candidates: {more:?}"),
        }
    }

    fn has_marker(self, marker: &str) -> bool {
        let marker = Identifier::new_intern(marker);
        self.graph().desc.type_info.values()
            .any(|t| t.markers.contains(&marker))
            || self.graph().desc.controllers.values().any(|c|
                c.markers.values().any(|m| m.contains(&marker))
            )
    }
}

pub struct PreFrg {
    pub desc: ProgramDescription,
    pub name_map: crate::HashMap<Identifier, Vec<crate::DefId>>,
}

impl<'g> HasGraph<'g> for &'g PreFrg {
    fn graph(self) -> &'g PreFrg {
        self
    }
}

impl PreFrg {
    pub fn from_file_at(dir: &str) -> Self {
        use_rustc(|| {
            let desc: ProgramDescription = serde_json::from_reader(
                &mut std::fs::File::open(format!("{dir}/{}", crate::consts::FLOW_GRAPH_OUT_NAME))
                    .unwrap(),
            )
            .unwrap();
            let name_map = desc
                .def_info
                .iter()
                .map(|(def_id, info)| (info.name, *def_id))
                .into_group_map();
            Self { desc, name_map }
        })
    }
}

#[derive(Clone)]
pub struct CtrlRef<'g> {
    graph: &'g PreFrg,
    ident: Identifier,
    ctrl: &'g crate::desc::SPDG,
}

impl<'g> PartialEq for CtrlRef<'g> {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident
    }
}

impl<'g> HasGraph<'g> for &CtrlRef<'g> {
    fn graph(self) -> &'g PreFrg {
        self.graph.graph()
    }
}

impl<'g> CtrlRef<'g> {
    pub fn call_sites(&'g self, fun: &'g FnRef<'g>) -> Vec<CallStringRef<'g>> {
        let mut all: Vec<CallStringRef<'g>> = self
            .ctrl
            .graph
            .edge_references()
            .map(|v| v.weight().at)
            .filter(|m| m.leaf().function.to_def_id() == fun.ident )
            .map(|call_site| {
                CallStringRef {
                    ctrl: self,
                    call_site,
                }
            })
            .collect();
        all.dedup_by_key(|r| r.call_site);
        all
    }

    pub fn call_site(&'g self, fun: &'g FnRef<'g>) -> CallSiteRef<'g> {
        let mut cs = self.call_sites(fun);
        assert!(
            cs.len() == 1,
            "expected only one call site for {}, found {}",
            fun.info_for(fun.ident).name,
            cs.len()
        );
        cs.pop().unwrap()
    }

    pub fn types_for(&'g self, target: &Node) -> &[DefId] {
        self.ctrl.types.get(target).map_or(&[], |t| t.0.as_slice())
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

impl<'g> PartialEq<crate::desc::CallString> for CallStringRef<'g> {
    fn eq(&self, other: &crate::desc::CallString) -> bool {
        self.call_site == *other
    }
}

impl<'g> CallStringRef<'g> {
    pub fn input(&'g self) -> Vec<NodeRef<'g>> {
        let graph = &self.ctrl.ctrl.graph;
        let mut all: Vec<_> = graph
            .edge_references()
            .filter(|e|
                e.weight().at == self.call_site
            )
            .filter_map(|e| {
                let src = graph.node_weight(e.source())?;
                Some((src.argument?, e.source()))
            })
            .collect();
        all.sort_by_key(|s| s.0);
        all
    }

    pub fn output(&self) -> NodeRef<'g> {

    }

    pub fn flows_to(&self, sink: &NodeRef) -> bool {

    }
    pub fn call_site(&self) -> crate::desc::CallString {
        self.call_site
    }
}

impl<'g> HasGraph<'g> for &CallSiteRef<'g> {
    fn graph(self) -> &'g PreFrg {
        self.function.graph()
    }
}

pub struct NodeRef<'g> {
    node: Node,
    controller: DefId,
    graph: &'g PreFrg,
}

impl<'g> HasGraph<'g> for &NodeRef<'g> {
    fn graph(self) -> &'g PreFrg {
        self.graph
    }
}
