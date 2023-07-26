#![allow(dead_code)]
extern crate either;
extern crate rustc_hir as hir;
extern crate rustc_middle;
extern crate rustc_span;
use dfpp::{
    desc::{DataSink, Identifier, ProgramDescription},
    ir::{GlobalLocationS, IsGlobalLocation, RawGlobalLocation},
    serializers::Bodies,
    HashSet, Symbol,
};
use hir::BodyId;
use rustc_middle::mir;

use either::Either;

use dfpp::utils::outfile_pls;
use std::borrow::Cow;
use std::io::prelude::*;

lazy_static! {
    pub static ref CWD_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());
    pub static ref DFPP_INSTALLED: bool = install_dfpp();
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

/// Run the action `F` in directory `P` and with rustc data structures
/// initialized (e.g. using [`Symbol`] works), taking care to lock the directory
/// change and resetting the working directory after.
///
/// Be aware that any [`Symbol`] created in `F` will **not** compare equal to
/// [`Symbol`]s created after `F` and may cause dereference errors.
pub fn cwd_and_use_rustc_in<
    P: AsRef<std::path::Path>,
    A,
    F: std::panic::UnwindSafe + FnOnce() -> A,
>(
    p: P,
    f: F,
) -> std::io::Result<A> {
    with_current_directory(p, || {
        eprintln!("creating session");
        rustc_span::create_default_session_if_not_set_then(|_| f())
    })
}

/// Initialize rustc data structures (e.g. [`Symbol`] works) and run `F`
///
/// Be aware that any [`Symbol`] created in `F` will **not** compare equal to
/// [`Symbol`]s created after `F` and may cause dereference errors.
pub fn use_rustc<A, F: FnOnce() -> A>(f: F) -> A {
    rustc_span::create_default_session_if_not_set_then(|_| f())
}

pub fn install_dfpp() -> bool {
    std::process::Command::new("cargo")
        .arg("install")
        .arg("--locked")
        .arg("--offline")
        .arg("--path")
        .arg(".")
        .arg("--debug")
        .status()
        .unwrap()
        .success()
}

/// Run dfpp in the current directory, passing the
/// `--dump-serialized-non-transitive-graph` flag, which dumps a
/// [`CallOnlyFlow`](dfpp::ir::flows::CallOnlyFlow) for each controller.
///
/// The result is suitable for reading with
/// [`read_non_transitive_graph_and_body`](dfpp::dbg::read_non_transitive_graph_and_body).
pub fn run_dfpp_with_graph_dump() -> bool {
    run_dfpp_with_graph_dump_and::<_, &str>([])
}

/// Run dfpp in the current directory, passing the
/// `--dump-serialized-non-transitive-graph` flag, which dumps a
/// [`CallOnlyFlow`](dfpp::ir::flows::CallOnlyFlow) for each controller.
///
/// The result is suitable for reading with
/// [`read_non_transitive_graph_and_body`](dfpp::dbg::read_non_transitive_graph_and_body).
///
/// Allows for additional arguments to be passed to dfpp
pub fn run_dfpp_with_graph_dump_and<I, S>(extra: I) -> bool
where
    I: IntoIterator<Item = S>,
    S: AsRef<std::ffi::OsStr>,
{
    std::process::Command::new("cargo")
        .arg("dfpp")
        .arg("--abort-after-analysis")
        .arg("--dump-serialized-non-transitive-graph")
        .args(extra)
        .status()
        .unwrap()
        .success()
}
/// Run dfpp in the current directory, passing the
/// `--dump-serialized-flow-graph` which dumps the [`ProgramDescription`] as
/// JSON.
///
/// The result is suitable for reading with [`PreFrg::from_file_at`]
pub fn run_dfpp_with_flow_graph_dump() -> bool {
    run_dfpp_with_flow_graph_dump_and::<_, &str>([])
}

/// Run dfpp in the current directory, passing the
/// `--dump-serialized-flow-graph` which dumps the [`ProgramDescription`] as
/// JSON.
///
/// The result is suitable for reading with [`PreFrg::from_file_at`]
pub fn run_dfpp_with_flow_graph_dump_and<I, S>(extra: I) -> bool
where
    I: IntoIterator<Item = S>,
    S: AsRef<std::ffi::OsStr>,
{
    std::process::Command::new("cargo")
        .arg("dfpp")
        .arg("--abort-after-analysis")
        .arg("--dump-serialized-flow-graph")
        .args(extra)
        .status()
        .unwrap()
        .success()
}

/// Define a test that is skipped. This can be used to temporarily disable the
/// test. A message can be passed after the test name explaining why it was
/// skipped and the message will be printed when the test is skipped.
#[macro_export]
macro_rules! define_test_skip {
    ($name:ident : $graph:ident -> $block:block) => {
        define_test_skip!($name "" : $graph -> $block);
    };
    ($name:ident $message:literal : $graph:ident -> $block:block) => {
        #[test]
        fn $name() {
            eprintln!(concat!("Skipping test ", stringify!($name), " ", $message));
        }
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

pub fn run_forge(file: &str) -> bool {
    std::process::Command::new("racket")
        .arg(file)
        .stdout(std::process::Stdio::piped())
        .status()
        .unwrap()
        .success()
}

pub fn write_forge(file: &str, property: &str, result: &str) -> Result<(), std::io::Error> {
    let content = format!(
        "#lang forge 

open \"helpers.frg\"
open \"analysis_result.frg\"

test expect {{
	property_test: {{
		{}
	}} for {} is {}
}}
	",
        property,
        dfpp::frg::name::FLOWS_PREDICATE,
        result
    );

    outfile_pls(file).and_then(|mut f| f.write_all(content.as_bytes()))
}

use dfpp::serializers::SerializableCallOnlyFlow;

/// A deserialized version of [`CallOnlyFlow`](dfpp::ir::flows::CallOnlyFlow)
pub struct G {
    pub graph: SerializableCallOnlyFlow,
    pub body: Bodies,
    pub ctrl_name: Symbol,
}

pub trait GetCallSites {
    fn get_call_sites<'a>(
        &'a self,
        g: &'a SerializableCallOnlyFlow,
    ) -> HashSet<&'a RawGlobalLocation>;
}

impl GetCallSites for RawGlobalLocation {
    fn get_call_sites<'a>(
        &'a self,
        _: &'a SerializableCallOnlyFlow,
    ) -> HashSet<&'a RawGlobalLocation> {
        [self].into_iter().collect()
    }
}

impl GetCallSites for GlobalLocationS {
    fn get_call_sites<'a>(
        &'a self,
        g: &'a SerializableCallOnlyFlow,
    ) -> HashSet<&'a RawGlobalLocation> {
        g.all_locations_iter()
            .filter(move |l| l.innermost() == *self)
            .collect()
    }
}

pub trait MatchCallSite {
    fn match_(&self, call_site: &RawGlobalLocation) -> bool;
}

impl MatchCallSite for RawGlobalLocation {
    fn match_(&self, call_site: &RawGlobalLocation) -> bool {
        self == call_site
    }
}

impl MatchCallSite for GlobalLocationS {
    fn match_(&self, call_site: &RawGlobalLocation) -> bool {
        *self == call_site.innermost()
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
    fn predecessors(&self, n: &RawGlobalLocation) -> impl Iterator<Item = &RawGlobalLocation> {
        self.predecessors_configurable(n, EdgeSelection::Both)
    }

    pub fn connects_none_configurable<From: MatchCallSite>(
        &self,
        n: &From,
        dir: EdgeSelection,
    ) -> bool {
        self.graph.location_dependencies.iter().all(|(c, deps)| {
            (!n.match_(c)
                || dir
                    .use_data()
                    .then_some(deps.input_deps.iter())
                    .into_iter()
                    .flatten()
                    .chain(
                        dir.use_control()
                            .then_some([&deps.ctrl_deps].into_iter())
                            .into_iter()
                            .flatten(),
                    )
                    .all(|d| d.is_empty()))
                && dir
                    .use_data()
                    .then_some(deps.input_deps.iter())
                    .into_iter()
                    .flatten()
                    .chain(
                        dir.use_control()
                            .then_some([&deps.ctrl_deps].into_iter())
                            .into_iter()
                            .flatten(),
                    )
                    .flat_map(|d| d.iter())
                    .all(|d| !n.match_(d))
        })
    }

    pub fn connects_none<From: MatchCallSite>(&self, n: &From) -> bool {
        self.connects_none_configurable(n, EdgeSelection::Both)
    }

    fn predecessors_configurable(
        &self,
        n: &RawGlobalLocation,
        con_ty: EdgeSelection,
    ) -> impl Iterator<Item = &RawGlobalLocation> {
        self.graph
            .location_dependencies
            .get(n)
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
                    .flat_map(|s| s.iter())
            })
    }
    pub fn connects<From: MatchCallSite, To: GetCallSites>(&self, from: &From, to: &To) -> bool {
        self.connects_configurable(from, to, EdgeSelection::Both)
    }

    pub fn connects_data<From: MatchCallSite, To: GetCallSites>(
        &self,
        from: &From,
        to: &To,
    ) -> bool {
        self.connects_configurable(from, to, EdgeSelection::Data)
    }

    pub fn connects_ctrl<From: MatchCallSite, To: GetCallSites>(
        &self,
        from: &From,
        to: &To,
    ) -> bool {
        self.connects_configurable(from, to, EdgeSelection::Control)
    }

    /// Is there any path (using directed edges) from `from` to `to`.
    pub fn connects_configurable<From: MatchCallSite, To: GetCallSites>(
        &self,
        from: &From,
        to: &To,
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
    pub fn connects_direct_data<From: MatchCallSite, To: GetCallSites>(
        &self,
        from: &From,
        to: &To,
    ) -> bool {
        self.connects_direct_configurable(from, to, EdgeSelection::Data)
    }

    pub fn connects_direct<From: MatchCallSite, To: GetCallSites>(
        &self,
        from: &From,
        to: &To,
    ) -> bool {
        self.connects_direct_configurable(from, to, EdgeSelection::Both)
    }

    pub fn connects_direct_ctrl<From: MatchCallSite, To: GetCallSites>(
        &self,
        from: &From,
        to: &To,
    ) -> bool {
        self.connects_direct_configurable(from, to, EdgeSelection::Control)
    }

    fn connects_direct_configurable<From: MatchCallSite, To: GetCallSites>(
        &self,
        from: &From,
        to: &To,
        typ: EdgeSelection,
    ) -> bool {
        for to in to.get_call_sites(&self.graph).iter() {
            if self
                .predecessors_configurable(to, typ)
                .any(|l| from.match_(l))
            {
                return true;
            }
        }
        false
    }

    pub fn returns_direct<From: MatchCallSite>(&self, from: &From) -> bool {
        self.graph
            .return_dependencies
            .iter()
            .any(|d| from.match_(d))
    }

    pub fn returns<From: MatchCallSite>(&self, from: &From) -> bool {
        self.returns_direct(from)
            || self
                .graph
                .return_dependencies
                .iter()
                .any(|r| self.connects(from, r))
    }

    /// Return all call sites for functions with names matching `pattern`.
    pub fn function_calls(&self, pattern: &str) -> HashSet<GlobalLocationS> {
        self.body
            .0
            .iter()
            .flat_map(|(bid, body)| {
                body.1
                     .0
                    .iter()
                    .filter(|s| s.1.contains(pattern))
                    .map(|s| GlobalLocationS {
                        function: *bid,
                        location: s.0,
                    })
            })
            .collect()
    }

    /// Like `function_calls` but requires that only one such call is found.
    pub fn function_call(&self, pattern: &str) -> GlobalLocationS {
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
        let (graph, body) = dfpp::dbg::read_non_transitive_graph_and_body(
            std::fs::File::open(format!("{}.ntgb.json", s.as_str())).unwrap(),
        );
        Self {
            graph,
            body,
            ctrl_name: s,
        }
    }
    pub fn ctrl(&self) -> BodyId {
        *self
            .body
            .0
            .iter()
            .find_map(|(id, (name, _))| (*name == self.ctrl_name).then_some(id))
            .unwrap()
    }
    /// Get the `n`th argument for this `bid` body.
    pub fn argument(&self, bid: BodyId, n: usize) -> mir::Location {
        let body = &self.body.0[&bid];
        body.1
             .0
            .iter()
            .find(|(_, s, _)| s == format!("Argument _{n}").as_str())
            .unwrap_or_else(|| panic!("Argument {n} not found in {:?}", body))
            .0
    }
}

pub trait HasGraph<'g>: Sized + Copy {
    fn graph(self) -> &'g PreFrg;

    fn function(self, name: &str) -> FnRef<'g> {
        FnRef {
            graph: self.graph(),
            ident: Identifier::new_intern(name),
        }
    }

    fn ctrl(self, name: &str) -> CtrlRef<'g> {
        let ident = Identifier::new_intern(name);
        CtrlRef {
            graph: self.graph(),
            ident,
            ctrl: &self.graph().0.controllers[&self.ctrl_hashed(name)],
        }
    }

    fn ctrl_hashed(self, name: &str) -> Identifier {
        match self
            .graph()
            .0
            .controllers
            .iter()
            .filter(|(id, _)| id.as_str().starts_with(name) && id.as_str().len() == name.len() + 7)
            .map(|i| i.0)
            .collect::<Vec<_>>()
            .as_slice()
        {
            [] => panic!("Could not find controller '{name}'"),
            [ctrl] => **ctrl,
            more => panic!("Too many matching controllers, found candidates: {more:?}"),
        }
    }

    fn has_marker(self, marker: &str) -> bool {
        let marker = Symbol::intern(marker);
        self.graph().0.annotations.values().any(|v| {
            v.0.iter()
                .filter_map(|a| a.as_label_ann())
                .any(|m| m.marker == marker)
        })
    }
}

pub struct PreFrg(ProgramDescription);

impl<'g> HasGraph<'g> for &'g PreFrg {
    fn graph(self) -> &'g PreFrg {
        self
    }
}

impl PreFrg {
    pub fn from_file_at(dir: &str) -> Self {
        use_rustc(|| {
            Self(
                serde_json::from_reader(
                    &mut std::fs::File::open(format!(
                        "{dir}/{}",
                        dfpp::consts::FLOW_GRAPH_OUT_NAME
                    ))
                    .unwrap(),
                )
                .unwrap(),
            )
        })
    }
}

#[derive(Clone)]
pub struct CtrlRef<'g> {
    graph: &'g PreFrg,
    ident: Identifier,
    ctrl: &'g dfpp::desc::Ctrl,
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
    pub fn call_sites(&'g self, fun: &'g FnRef<'g>) -> Vec<CallSiteRef<'g>> {
        let mut all: Vec<CallSiteRef<'g>> = self
            .ctrl
            .data_flow
            .0
            .values()
            .flat_map(|v| {
                v.iter()
                    .filter_map(DataSink::as_argument)
                    .map(|sink| CallSiteRef {
                        function: fun,
                        call_site: sink.0,
                        ctrl: Cow::Borrowed(self),
                    })
            })
            .chain(
                self.ctrl
                    .data_flow
                    .0
                    .keys()
                    .filter_map(dfpp::desc::DataSource::as_function_call)
                    .map(|f| CallSiteRef {
                        function: fun,
                        call_site: f,
                        ctrl: Cow::Borrowed(self),
                    }),
            )
            .chain(
                self.ctrl
                    .ctrl_flow
                    .0
                    .keys()
                    .filter_map(dfpp::desc::DataSource::as_function_call)
                    .map(|f| CallSiteRef {
                        function: fun,
                        call_site: f,
                        ctrl: Cow::Borrowed(self),
                    }),
            )
            .chain(
                self.ctrl
                    .ctrl_flow
                    .0
                    .values()
                    .flat_map(|cs_map| cs_map.iter())
                    .map(|f| CallSiteRef {
                        function: fun,
                        call_site: f,
                        ctrl: Cow::Borrowed(self),
                    }),
            )
            .filter(|ref_| {
                ref_.call_site
                    .function
                    .as_str()
                    .starts_with(ref_.function.ident.as_str())
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
            fun.ident,
            cs.len()
        );
        cs.pop().unwrap()
    }
}

impl<'g> HasGraph<'g> for &FnRef<'g> {
    fn graph(self) -> &'g PreFrg {
        self.graph.graph()
    }
}

pub struct FnRef<'g> {
    graph: &'g PreFrg,
    ident: Identifier,
}

impl<'g> FnRef<'g> {
    fn graph(&self) -> &'g PreFrg {
        self.graph.graph()
    }
}

pub struct CallSiteRef<'g> {
    function: &'g FnRef<'g>,
    call_site: &'g dfpp::desc::CallSite,
    ctrl: Cow<'g, CtrlRef<'g>>,
}

impl<'g> PartialEq<dfpp::desc::CallSite> for CallSiteRef<'g> {
    fn eq(&self, other: &dfpp::desc::CallSite) -> bool {
        self.call_site == other
    }
}

impl<'g> CallSiteRef<'g> {
    pub fn input(&'g self) -> Vec<DataSinkRef<'g>> {
        let mut all: Vec<_> = self
            .ctrl
            .ctrl
            .data_flow
            .0
            .values()
            .flat_map(|s| s.iter())
            .filter(|s| matches!(s, DataSink::Argument {function, ..} if self == function))
            .map(|s| DataSinkRef {
                call_site: Either::Left(self),
                sink: s,
            })
            .collect();
        all.sort_by_key(|s| s.sink.as_argument().unwrap().1);
        all
    }

    pub fn flows_to(&self, sink: &DataSinkRef) -> bool {
        let next_hop = |src: dfpp::desc::CallSite| {
            self.ctrl
                .ctrl
                .data_flow
                .0
                .get(&dfpp::desc::DataSource::FunctionCall(src.clone()))
                .iter()
                .flat_map(|i| i.iter())
                .map(Either::Left)
                .chain(
                    self.ctrl
                        .ctrl
                        .ctrl_flow
                        .0
                        .get(&dfpp::desc::DataSource::FunctionCall(src))
                        .iter()
                        .flat_map(|i| i.iter())
                        .map(Either::Right),
                )
                .collect()
        };

        let mut seen = HashSet::new();
        let mut queue: Vec<_> = next_hop(self.call_site.clone());
        while let Some(n) = queue.pop() {
            if match n {
                Either::Left(l) => sink == l,
                _ => false,
            } {
                return true;
            }

            if !seen.contains(&n) {
                seen.insert(n);
                match n {
                    Either::Left(l) => {
                        if let Some((fun, _)) = l.as_argument() {
                            queue.extend(next_hop(fun.clone()))
                        }
                    }
                    Either::Right(r) => queue.extend(next_hop(r.clone())),
                };
            }
        }
        false
    }
}

impl<'g> HasGraph<'g> for &CallSiteRef<'g> {
    fn graph(self) -> &'g PreFrg {
        self.function.graph()
    }
}

pub struct DataSinkRef<'g> {
    call_site: Either<&'g CallSiteRef<'g>, &'g PreFrg>,
    sink: &'g dfpp::desc::DataSink,
}

impl<'g> HasGraph<'g> for &DataSinkRef<'g> {
    fn graph(self) -> &'g PreFrg {
        match self.call_site {
            Either::Left(l) => l.graph(),
            Either::Right(r) => r.graph(),
        }
    }
}

impl PartialEq<dfpp::desc::DataSink> for DataSinkRef<'_> {
    fn eq(&self, other: &dfpp::desc::DataSink) -> bool {
        self.sink == other
    }
}
