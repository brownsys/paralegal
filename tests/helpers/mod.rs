extern crate either;
extern crate rustc_hir as hir;
extern crate rustc_middle;
extern crate rustc_span;
use dfpp::{
    desc::{DataSink, Identifier, ProgramDescription},
    serializers::{Bodies, RawGlobalLocation},
    HashMap, HashSet, ir::IsGlobalLocation, Symbol,
};
use hir::BodyId;
use rustc_middle::mir;

use either::Either;

use std::borrow::Cow;

lazy_static! {
    static ref CWD_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());
    pub static ref DFPP_INSTALLED: bool = install_dfpp();
}

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
    let res = std::panic::catch_unwind(f);
    let set_dir = std::env::set_current_dir(current);
    match res {
        Ok(r) => set_dir.map(|()| r),
        Err(e) => std::panic::resume_unwind(e),
    }
}

pub fn cwd_and_use_rustc_in<
    P: AsRef<std::path::Path>,
    A,
    F: std::panic::UnwindSafe + FnOnce() -> A,
>(
    p: P,
    f: F,
) -> std::io::Result<A> {
    with_current_directory(p, || {
        rustc_span::create_default_session_if_not_set_then(|_| f())
    })
}

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

pub fn run_dfpp_with_graph_dump() -> bool {
    std::process::Command::new("cargo")
        .arg("dfpp")
        .arg("--dump-serialized-non-transitive-graph")
        .status()
        .unwrap()
        .success()
}

pub fn run_dfpp_with_flow_graph_dump() -> bool {
    std::process::Command::new("cargo")
        .arg("dfpp")
        .arg("--dump-serialized-flow-graph")
        .status()
        .unwrap()
        .success()
}

use dfpp::serializers::SerializableCallOnlyFlow;

pub struct G {
    pub graph: SerializableCallOnlyFlow,
    pub body: Bodies,
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

impl GetCallSites for (mir::Location, hir::BodyId) {
    fn get_call_sites<'a>(
        &'a self,
        g: &'a SerializableCallOnlyFlow,
    ) -> HashSet<&'a RawGlobalLocation> {
        g.all_locations_iter()
            .filter(move |l| l.innermost_location_and_body() == *self)
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

impl MatchCallSite for (mir::Location, hir::BodyId) {
    fn match_(&self, call_site: &RawGlobalLocation) -> bool {
        *self == call_site.innermost_location_and_body()
    }
}

impl G {
    fn predecessors(&self, n: &RawGlobalLocation) -> impl Iterator<Item = &RawGlobalLocation> {
        self.graph.0.get(&n).into_iter().flat_map(|deps| {
            std::iter::once(&deps.ctrl_deps)
                .chain(deps.input_deps.iter())
                .flat_map(|s| s.iter())
        })
    }
    pub fn connects<From: MatchCallSite, To: GetCallSites>(&self, from: &From, to: &To) -> bool {
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
            if from.match_(n) {
                return true;
            }
            queue.extend(self.predecessors(n))
        }
        false
    }

    pub fn connects_direct<From: MatchCallSite, To: GetCallSites>(
        &self,
        from: &From,
        to: &To,
    ) -> bool {
        for to in to.get_call_sites(&self.graph).iter() {
            if self.predecessors(to).any(|l| from.match_(l)) {
                return true;
            }
        }
        false
    }

    pub fn function_calls(&self, pattern: &str) -> HashSet<(mir::Location, hir::BodyId)> {
        self.body
            .0
            .iter()
            .flat_map(|(bid, body)| {
                body.0
                    .iter()
                    .filter(|s| s.1.contains(pattern))
                    .map(|s| (s.0, *bid))
            })
            .collect()
    }

    pub fn function_call(&self, pattern: &str) -> (mir::Location, hir::BodyId) {
        let v = self.function_calls(pattern);
        assert!(
            v.len() == 1,
            "function '{pattern}' should only occur once in {v:?}"
        );
        v.into_iter().next().unwrap()
    }

    pub fn from_file(s: Symbol) -> Self {
        let (graph, body) = dfpp::dbg::read_non_transitive_graph_and_body(
            std::fs::File::open(format!("{}.ntgb.json", s.as_str())).unwrap(),
        );
        Self { graph, body }
    }
    pub fn argument(&self, bid: BodyId, n: usize) -> mir::Location {
        self.body.0[&bid]
            .0
            .iter()
            .find(|(_, s, _)| s == format!("Argument _{n}").as_str())
            .unwrap_or_else(|| panic!("Argument {n} not found in {:?}", self.body.0[&bid]))
            .0
    }
}

pub trait HasGraph<'g> {
    fn graph(self) -> &'g ProgramDescription;
}

pub struct PreFrg(ProgramDescription);

impl<'g> HasGraph<'g> for &'g PreFrg {
    fn graph(self) -> &'g ProgramDescription {
        &self.0
    }
}

impl PreFrg {
    pub fn from_file_at(dir: &str) -> Self {
        use_rustc(|| {
            Self(
                serde_json::from_reader(
                    &mut std::fs::File::open(format!("{dir}/{}", dfpp::FLOW_GRAPH_OUT_NAME))
                        .unwrap(),
                )
                .unwrap(),
            )
        })
    }

    pub fn function(&self, name: &str) -> FnRef {
        FnRef {
            graph: self,
            ident: Identifier::from_str(name),
        }
    }

    pub fn ctrl(&self, name: &str) -> CtrlRef {
        let ident = Identifier::from_str(name);
        CtrlRef {
            graph: self,
            ident,
            ctrl: &self.0.controllers[&ident],
        }
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
    fn graph(self) -> &'g ProgramDescription {
        self.graph.graph()
    }
}

impl<'g> CtrlRef<'g> {
    pub fn call_sites(&'g self, fun: &'g FnRef<'g>) -> Vec<CallSiteRef<'g>> {
        let mut all: Vec<CallSiteRef<'g>> = self
            .ctrl
            .flow
            .0
            .values()
            .flat_map(|v| {
                v.iter()
                    .filter_map(DataSink::as_argument)
                    .map(|sink| CallSiteRef {
                        function: fun,
                        call_site: &sink.0,
                        ctrl: Cow::Borrowed(self),
                    })
            })
            .chain(
                self.ctrl
                    .flow
                    .0
                    .keys()
                    .filter_map(dfpp::desc::DataSource::as_function_call)
                    .map(|f| CallSiteRef {
                        function: fun,
                        call_site: f,
                        ctrl: Cow::Borrowed(self),
                    }),
            )
            .filter(|ref_| ref_.function.ident == ref_.call_site.function)
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
    fn graph(self) -> &'g ProgramDescription {
        self.graph.graph()
    }
}

pub struct FnRef<'g> {
    graph: &'g PreFrg,
    ident: Identifier,
}

impl<'g> FnRef<'g> {
    fn graph(&self) -> &'g ProgramDescription {
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
            .flow
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
        let mut seen = HashSet::new();
        let mut queue: Vec<_> = self
            .ctrl
            .ctrl
            .flow
            .0
            .get(&dfpp::desc::DataSource::FunctionCall(
                self.call_site.clone(),
            ))
            .iter()
            .flat_map(|i| i.iter())
            .collect();
        while let Some(n) = queue.pop() {
            if sink == n {
                return true;
            }
            if !seen.contains(n) {
                seen.insert(n);
                if let Some((fun, _)) = n.as_argument() {
                    queue.extend(
                        self.ctrl
                            .ctrl
                            .flow
                            .0
                            .get(&dfpp::desc::DataSource::FunctionCall(fun.clone()))
                            .iter()
                            .flat_map(|s| s.iter()),
                    );
                }
            }
        }
        false
    }
}

impl<'g> HasGraph<'g> for &CallSiteRef<'g> {
    fn graph(self) -> &'g ProgramDescription {
        self.function.graph()
    }
}

pub struct DataSinkRef<'g> {
    call_site: Either<&'g CallSiteRef<'g>, &'g PreFrg>,
    sink: &'g dfpp::desc::DataSink,
}

impl<'g> HasGraph<'g> for &DataSinkRef<'g> {
    fn graph(self) -> &'g ProgramDescription {
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
