#![allow(dead_code)]
extern crate either;
extern crate rustc_hir as hir;
extern crate rustc_middle;
extern crate rustc_span;

use hir::def_id::DefId;
use rustc_interface::interface;

use crate::{
    ann::dump_markers,
    desc::{Identifier, ProgramDescription},
    utils::Print,
    Callbacks, HashSet, EXTRA_RUSTC_ARGS,
};
use std::hash::{Hash, Hasher};
use std::process::Command;
use std::{
    fmt::{Debug, Formatter},
    sync::Once,
};

use paralegal_spdg::{
    traverse::{generic_flows_to, generic_influencers, EdgeSelection},
    utils::write_sep,
    DefInfo, EdgeInfo, Endpoint, Node, TypeId, SPDG,
};

use flowistry_pdg::CallString;
use itertools::Itertools;
use petgraph::visit::{Control, Data, DfsEvent, EdgeRef, FilterEdge, GraphBase, IntoEdges};
use petgraph::visit::{IntoNeighbors, IntoNodeReferences};
use petgraph::visit::{NodeRef as _, Visitable};
use std::path::Path;

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

/// Crates a basic invocation of `cargo paralegal-flow`, ensuring that the `cargo-paralegal-flow`
/// and `paralegal-flow` executables that were built from this project are (first) in the
/// `PATH`.
pub fn paralegal_flow_command(dir: impl AsRef<Path>) -> std::process::Command {
    // Force paralegal-flow binary to be built
    let success = Command::new("cargo")
        .args(["build", "-p", "paralegal-flow"])
        .status()
        .unwrap()
        .success();
    assert!(success);
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
    let mut cmd = Command::new(cargo_paralegal_flow_path);
    cmd.arg("paralegal-flow")
        .env("PATH", new_path)
        .current_dir(dir);
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
    assert!(Command::new("cargo")
        .arg("clean")
        .current_dir(dir)
        .status()
        .unwrap()
        .success());
    paralegal_flow_command(dir)
        .args(["--abort-after-analysis"])
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
            use_rustc(|| {
                let graph = PreFrg::from_file_at($crate_name);
                let $ctrl = graph.ctrl(stringify!($ctrl_name));
                $block
            })
        }
    };
}

/// Builder for running test cases against a string of source code.
///
/// Start with [`InlineTestBuilder::new`], compile and run the test case with
/// [`InlineTestBuilder::check`].
pub struct InlineTestBuilder {
    ctrl_name: String,
    input: String,
    extra_args: Vec<String>,
}

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
            ctrl_name: "crate::main".into(),
            extra_args: Default::default(),
        }
    }

    /// Chose a function as analysis entrypoint. Overwrites any previous choice
    /// without warning.
    pub fn with_entrypoint(&mut self, name: impl Into<String>) -> &mut Self {
        self.ctrl_name = name.into();
        self
    }

    pub fn with_extra_args(&mut self, args: impl IntoIterator<Item = String>) -> &mut Self {
        self.extra_args.extend(args);
        self
    }

    pub fn expect_fail_compile(&self) {
        let reached = Once::new();
        let res = self.run(|_| reached.call_once(|| ()));
        assert!(res.is_err(), "the compiler existed successfully");
    }

    /// Compile the code, select the [`CtrlRef`] corresponding to the configured
    /// entrypoint and hand it to the `check` function which should contain the
    /// test predicate.
    pub fn check_ctrl(&self, check: impl FnOnce(CtrlRef) + Send) {
        self.run(|graph| {
            let cref = graph.ctrl(&self.ctrl_name);
            check(cref);
        })
        .unwrap()
    }

    pub fn run(&self, f: impl FnOnce(PreFrg) + Send) -> interface::Result<()> {
        use clap::Parser;

        #[derive(clap::Parser)]
        struct TopLevelArgs {
            #[clap(flatten)]
            args: crate::ClapArgs,
        }

        let args = ["".into(), "--analyze".into(), self.ctrl_name.to_string()]
            .into_iter()
            .chain(self.extra_args.iter().cloned())
            .collect::<Vec<_>>();

        let args = crate::Args::try_from(TopLevelArgs::parse_from(args).args).unwrap();

        args.setup_logging();

        rustc_utils::test_utils::CompileBuilder::new(&self.input)
            .with_args(EXTRA_RUSTC_ARGS.iter().copied().map(ToOwned::to_owned))
            .with_args(["-Ztrack-diagnostics".to_string()])
            .with_query_override(None)
            .compile(move |result| {
                let args: &'static _ = Box::leak(Box::new(args));
                dump_markers(result.tcx);
                let tcx = result.tcx;
                let (pdg, _) = Callbacks::new(args, &mut None)
                    .run_in_context_without_writing_stats(tcx)
                    .unwrap();
                let graph = PreFrg::from_description(pdg);
                f(graph)
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
            Some([]) | None => panic!("Did not find name {name}"),
            _ => panic!("Found too many function matching name {name}"),
        };
        FnRef {
            graph: self.graph(),
            ident: id,
        }
    }

    fn async_function(self, name: impl AsRef<str>) -> FnRef<'g> {
        self.function(format!("{}_generator", name.as_ref()))
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
    pub fn from_file_at(dir: &str) -> Self {
        use_rustc(|| {
            let desc = ProgramDescription::canonical_read(format!(
                "{dir}/{}",
                paralegal_spdg::FLOW_GRAPH_OUT_NAME
            ))
            .unwrap();
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

impl<'g> Debug for CtrlRef<'g> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CtrlRef")
            .field("ident", &self.ctrl.name)
            .finish()
    }
}

impl<'g> PartialEq for CtrlRef<'g> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<'g> HasGraph<'g> for &CtrlRef<'g> {
    fn graph(self) -> &'g PreFrg {
        self.graph.graph()
    }
}

impl<'g> CtrlRef<'g> {
    pub fn return_value(&self) -> NodeRefs {
        // TODO only include mutable formal parameters?
        let nodes = self.ctrl.return_.to_vec();
        NodeRefs { nodes, graph: self }
    }

    pub fn returns(&self, other: &impl FlowsTo) -> bool {
        other.flows_to_data(&self.return_value())
    }

    pub fn marked(&self, marker: Identifier) -> NodeRefs<'_> {
        NodeRefs {
            nodes: self
                .ctrl
                .markers
                .iter()
                .filter(|(_, markers)| markers.contains(&marker))
                .map(|(n, _)| *n)
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
                    .map_or(false, |i| i.id == fun.ident)
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
            cs.len()
        );
        cs.pop().unwrap()
    }

    pub fn types_for(&'g self, target: Node) -> &[DefId] {
        self.ctrl
            .type_assigns
            .get(&target)
            .map_or(&[], |t| t.0.as_ref())
    }

    pub fn nodes_for_type(&self, typ: TypeId) -> NodeRefs {
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

impl<'g> PartialEq<CallString> for CallStringRef<'g> {
    fn eq(&self, other: &CallString) -> bool {
        self.call_site == *other
    }
}

impl<'g> CallStringRef<'g> {
    pub fn input(&'g self) -> NodeRefs<'g> {
        let graph = &self.ctrl.ctrl.graph;
        // Alternative??
        let mut nodes: Vec<_> = graph
            .edge_references()
            .filter(|e| e.weight().at == self.call_site)
            .map(|e| (e.weight().source_use, e.source()))
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
            list.entry(&format!("{n:?} {} @ {} ", weight.description, weight.at));
        }
        list.finish()
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

impl<'g> HasGraph<'g> for &NodeRef<'g> {
    fn graph(self) -> &'g PreFrg {
        self.graph.graph
    }
}

impl<'g> NodeRef<'g> {
    pub fn node(&self) -> Node {
        self.node
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
