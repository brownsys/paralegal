#![allow(dead_code)]
extern crate either;
extern crate rustc_hir as hir;
extern crate rustc_middle;
extern crate rustc_span;
use crate::{
    desc::{Identifier, ProgramDescription},
    ir::CallOnlyFlow,
    serializers::{Bodies, InstructionProxy},
    HashSet, Symbol,
};

use paralegal_spdg::{rustc_portable::DefId, DefInfo, Node, NodeKind, SPDG, EdgeInfo};
use rustc_middle::mir;

use crate::pdg::{CallString, GlobalLocation, RichLocation};
use itertools::Itertools;
use petgraph::visit::{Control, DfsEvent, EdgeFiltered, EdgeRef};
use std::path::Path;
use petgraph::graph::EdgeReference;
use crate::pdg::rustc_portable::LocalDefId;
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

    fn ctrl_hashed(self, name: &str) -> LocalDefId {
        let candidates = self.graph().desc.controllers.iter()
            .filter(|(id, info)| info.name.as_str() == name)
            .map(|(id, _)| *id)
            .collect::<Vec<_>>();
        match candidates.as_slice() {
            [] => panic!("Could not find controller '{name}'"),
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
    ctrl: &'g SPDG,
}

impl<'g> CtrlRef<'g> {
    pub fn return_value(&self) -> NodeRefs {
        let graph = &self.ctrl.graph;
        let nodes: Vec<_> = graph
            .edge_references()
            .filter(|e| {
                let cs = e.weight().at;
                cs.is_at_root() && cs.leaf().location.is_end()
            })
            .filter_map(|e| {
                let src = e.source();
                match graph.node_weight(src)?.kind {
                    NodeKind::FormalReturn => Some(()),
                    _ => None,
                }?;
                Some(src)
            })
            .collect();
        // TODO include mutable return variables?
        NodeRefs {
            nodes,
            graph: self,
        }
    }

    pub fn returns(&self, other: &impl FlowsTo) -> bool {
        other.flows_to_data(
            &self.return_value()
        )
    }
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
    pub fn spdg(&self) -> &'g crate::desc::SPDG {
        self.ctrl
    }

    pub fn call_sites(&'g self, fun: &'g FnRef<'g>) -> Vec<CallStringRef<'g>> {
        let simple_sites = self
            .graph
            .desc
            .instruction_info
            .iter()
            .filter_map(|(k, v)| (v.as_function_call()?.id == fun.ident).then_some(k))
            .collect::<HashSet<_>>();

        let mut all: Vec<CallStringRef<'g>> = self
            .ctrl
            .graph
            .edge_references()
            .map(|v| v.weight().at)
            .filter(|m| simple_sites.contains(&m.leaf()))
            .map(|call_site| CallStringRef {
                ctrl: self,
                call_site,
            })
            .collect();
        all.dedup_by_key(|r| r.call_site);
        all
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
        self.ctrl.types.get(&target).map_or(&[], |t| t.0.as_slice())
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

impl<'g> PartialEq<CallString> for CallStringRef<'g> {
    fn eq(&self, other: &CallString) -> bool {
        self.call_site == *other
    }
}

impl<'g> CallStringRef<'g> {
    pub fn input(&'g self) -> NodeRefs<'g> {
        let graph = &self.ctrl.ctrl.graph;
        let mut nodes: Vec<_> = graph
            .edge_references()
            .filter(|e| e.weight().at == self.call_site)
            .filter_map(|e| {
                let src = e.source();
                let index = match graph.node_weight(src)?.kind {
                    NodeKind::ActualParameter(p) => Some(p),
                    _ => None,
                }?;
                Some((src, index))
            })
            .flat_map(move |(src, idxes)| idxes.into_iter_set_in_domain().map(move |i| (src, i)))
            .collect();
        nodes.sort_by_key(|s| s.1);
        NodeRefs {
            nodes: nodes.into_iter().map(|t| t.0).collect(),
            graph: self.ctrl,
        }
    }

    pub fn output(&self) -> NodeRefs<'g> {
        let graph = &self.ctrl.ctrl.graph;
        let nodes: Vec<_> = graph
            .edge_references()
            .filter(|e| e.weight().at == self.call_site)
            .filter_map(|e| {
                let src = e.source();
                match graph.node_weight(src)?.kind {
                    NodeKind::ActualReturn => Some(()),
                    _ => None,
                }?;
                Some(src)
            })
            .collect();
        // TODO include mutable return variables?
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

pub struct NodeRefs<'g> {
    nodes: Vec<Node>,
    graph: &'g CtrlRef<'g>,
}

impl<'g> NodeRefs<'g> {
    pub fn nth(&self, i: usize) -> Option<NodeRef<'g>> {
        Some(NodeRef {
            graph: self.graph,
            node: *self.nodes.get(i)?,
        })
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
        self.graph.ident
    }
}

impl FlowsTo for NodeRefs<'_> {
    fn nodes(&self) -> &[Node] {
        self.nodes.as_slice()
    }

    fn spdg(&self) -> &SPDG {
        self.graph.ctrl
    }

    fn spdg_ident(&self) -> Identifier {
        self.graph.ident
    }
}

pub trait FlowsTo {
    fn nodes(&self) -> &[Node];
    fn spdg(&self) -> &SPDG;
    fn spdg_ident(&self) -> Identifier;

    fn flows_to_data(&self, other: &impl FlowsTo) -> bool {
        self.flows_to(other, EdgeSelection::Data)
    }

    fn flows_to_ctrl(&self, other: &impl FlowsTo) -> bool {
        self.flows_to(other, EdgeSelection::Control)
    }

    fn flows_to_any(&self, other: &impl FlowsTo) -> bool {
        self.flows_to(other, EdgeSelection::Both)
    }

    fn is_neighbor_ctrl(&self, other: &impl FlowsTo) -> bool {
        self.is_neighbor(other, EdgeSelection::Control)
    }

    fn is_neighbor_data(&self, other: &impl FlowsTo) -> bool {
        self.is_neighbor(other, EdgeSelection::Data)
    }

    fn is_neighbor_any(&self, other: &impl FlowsTo) -> bool {
        self.is_neighbor(other, EdgeSelection::Both)
    }

    fn is_neighbor(&self, other: &impl FlowsTo, edge_selection: EdgeSelection) -> bool {
        if self.spdg_ident() != other.spdg_ident() {
            return false;
        }
        let targets = other.nodes().iter().copied().collect::<HashSet<_>>();
        let mut starts = self.nodes().iter().copied().peekable();
        if starts.peek().is_none() {
            return false;
        }
        starts.any(|n|
            self.spdg().graph.edges(n)
                .filter(|e|
                    match edge_selection {
                        EdgeSelection::Data => {
                            e.weight().is_data()
                        }
                        EdgeSelection::Control => {
                            e.weight().is_control()
                        }
                        EdgeSelection::Both => {
                            true
                        }
                    }
                )
                .any(|e|
                    targets.contains(&e.target())
                )
        )
    }

    fn flows_to(&self, other: &impl FlowsTo, edge_selection: EdgeSelection) -> bool {
        if self.spdg_ident() != other.spdg_ident() {
            return false;
        }
        let targets = other.nodes().iter().copied().collect::<HashSet<_>>();
        let mut starts = self.nodes().iter().copied().peekable();
        if starts.peek().is_none() {
            return false;
        }
        fn data_only(e: EdgeReference<EdgeInfo>) -> bool {
            e.weight().is_data()
        }
        fn control_only(e: EdgeReference<EdgeInfo>) -> bool {
            e.weight().is_data()
        }
        fn all_edges(e: EdgeReference<EdgeInfo>) -> bool {
            e.weight().is_data()
        }
        type F = fn(EdgeReference<EdgeInfo>) -> bool;
        let graph = match edge_selection {
            EdgeSelection::Data => EdgeFiltered(&self.spdg().graph, data_only as F),
            EdgeSelection::Control => EdgeFiltered(&self.spdg().graph, control_only as F),
            EdgeSelection::Both => EdgeFiltered(&self.spdg().graph, all_edges as F),
        };
        let result =
            petgraph::visit::depth_first_search(&graph, starts, |event| match event {
                DfsEvent::Discover(d, _) if targets.contains(&d) => Control::Break(()),
                _ => Control::Continue,
            });
        matches!(result, Control::Break(()))
    }
}
