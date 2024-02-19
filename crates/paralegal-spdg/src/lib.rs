//! This crate defines the program dependence graph (PDG) generated by Paralegal.
//!
//! The top-level type is [`ProgramDescription`]. This type references multiple
//! types defined within the Rust compiler such as MIR locations. To avoid requiring
//! a `rustc_private` dependency on paralegal_spdg clients, we provide proxies in the
//! [`rustc_proxies`] module for all Rustc types within the PDG.

#![cfg_attr(feature = "rustc", feature(rustc_private))]

#[cfg(feature = "rustc")]
pub(crate) mod rustc {
    extern crate rustc_driver;
    pub extern crate rustc_hir as hir;
    pub extern crate rustc_index as index;
    pub extern crate rustc_middle as middle;
    pub extern crate rustc_span as span;
    pub use hir::def_id;
    pub use middle::mir;
}

extern crate strum;

pub use flowistry_pdg::*;

pub mod dot;
mod tiny_bitset;
pub mod traverse;
pub mod utils;

use internment::Intern;
use itertools::Itertools;
use rustc_portable::DefId;
use serde::{Deserialize, Serialize};
use std::{fmt, hash::Hash};

use utils::serde_map_via_vec;

pub use crate::tiny_bitset::TinyBitSet;
use flowistry_pdg::rustc_portable::LocalDefId;
use petgraph::graph::{EdgeIndex, EdgeReference, NodeIndex};
use petgraph::prelude::EdgeRef;
use petgraph::visit::IntoNodeIdentifiers;
pub use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};

pub type Endpoint = LocalDefId;
pub type TypeId = DefId;
pub type Function = Identifier;

/// Name of the file used for emitting the JSON serialized
/// [`ProgramDescription`](crate::ProgramDescription).
pub const FLOW_GRAPH_OUT_NAME: &str = "flow-graph.json";

/// Types of annotations we support.
///
/// Usually you'd expect one of those annotation types in any given situation.
/// For convenience the match methods [`Self::as_marker`], [`Self::as_otype`]
/// and [`Self::as_exception`] are provided. These are particularly useful in
/// conjunction with e.g. [`Iterator::filter_map`]
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Deserialize, Serialize, strum::EnumIs)]
pub enum Annotation {
    Marker(MarkerAnnotation),
    OType(#[cfg_attr(feature = "rustc", serde(with = "rustc_proxies::DefId"))] TypeId),
    Exception(ExceptionAnnotation),
}

impl Annotation {
    /// If this is an [`Annotation::Marker`], returns the underlying [`MarkerAnnotation`].
    pub fn as_marker(&self) -> Option<&MarkerAnnotation> {
        match self {
            Annotation::Marker(l) => Some(l),
            _ => None,
        }
    }

    /// If this is an [`Annotation::OType`], returns the underlying [`TypeId`].
    pub fn as_otype(&self) -> Option<TypeId> {
        match self {
            Annotation::OType(t) => Some(*t),
            _ => None,
        }
    }

    /// If this is an [`Annotation::Exception`], returns the underlying [`ExceptionAnnotation`].
    pub fn as_exception(&self) -> Option<&ExceptionAnnotation> {
        match self {
            Annotation::Exception(e) => Some(e),
            _ => None,
        }
    }
}

pub type VerificationHash = u128;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Serialize, Deserialize)]
pub struct ExceptionAnnotation {
    /// The value of the verification hash we found in the annotation. Is `None`
    /// if there was no verification hash in the annotation.
    pub verification_hash: Option<VerificationHash>,
}

/// A marker annotation and its refinements.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Serialize, Deserialize)]
pub struct MarkerAnnotation {
    /// The (unchanged) name of the marker as provided by the user
    pub marker: Identifier,
    #[serde(flatten)]
    pub refinement: MarkerRefinement,
}

fn const_false() -> bool {
    false
}

/// Refinements in the marker targeting. The default (no refinement provided) is
/// `on_argument == vec![]` and `on_return == false`, which is also what is
/// returned from [`Self::empty`].
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Deserialize, Serialize)]
pub struct MarkerRefinement {
    #[serde(default, with = "crate::tiny_bitset::pretty")]
    on_argument: TinyBitSet,
    #[serde(default = "const_false")]
    on_return: bool,
}

/// Disaggregated version of [`MarkerRefinement`]. Can be added to an existing
/// refinement [`MarkerRefinement::merge_kind`].
#[derive(Clone, Deserialize, Serialize)]
pub enum MarkerRefinementKind {
    Argument(#[serde(with = "crate::tiny_bitset::pretty")] TinyBitSet),
    Return,
}

impl MarkerRefinement {
    /// The default, empty aggregate refinement `Self { on_argument: vec![],
    /// on_return: false }`
    pub fn empty() -> Self {
        Self {
            on_argument: Default::default(),
            on_return: false,
        }
    }

    /// Merge the aggregate refinement with another discovered refinement and
    /// check that they do not overwrite each other.
    pub fn merge_kind(mut self, k: MarkerRefinementKind) -> Result<Self, String> {
        match k {
            MarkerRefinementKind::Argument(a) => {
                if self.on_argument.is_empty() {
                    self.on_argument = a;
                    Ok(self)
                } else {
                    Err(format!(
                        "Double argument annotation {:?} and {a:?}",
                        self.on_argument
                    ))
                }
            }
            MarkerRefinementKind::Return => {
                if !self.on_return {
                    self.on_return = true;
                    Ok(self)
                } else {
                    Err("Double on-return annotation".to_string())
                }
            }
        }
    }

    /// Get the refinements on arguments
    pub fn on_argument(&self) -> TinyBitSet {
        self.on_argument
    }

    /// Is this refinement targeting the return value?
    pub fn on_return(&self) -> bool {
        self.on_return
    }

    /// True if this refinement is empty, i.e. the annotation is targeting the
    /// item itself.
    pub fn on_self(&self) -> bool {
        self.on_argument.is_empty() && !self.on_return
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Serialize, Deserialize, strum::EnumIs)]
pub enum ObjectType {
    Function(usize),
    Type,
    Other,
}

impl ObjectType {
    /// If this is [`Self::Function`], then return the payload.
    pub fn as_function(&self) -> Option<usize> {
        match self {
            ObjectType::Function(f) => Some(*f),
            _ => None,
        }
    }
}

#[allow(dead_code)]
mod ser_localdefid_map {
    use serde::{Deserialize, Serialize};

    use flowistry_pdg::rustc_proxies;

    #[derive(Serialize, Deserialize)]
    struct Helper(#[serde(with = "rustc_proxies::LocalDefId")] super::LocalDefId);

    pub fn serialize<S: serde::Serializer, V: serde::Serialize>(
        map: &super::HashMap<super::LocalDefId, V>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        map.iter()
            .map(|(k, v)| (Helper(*k), v))
            .collect::<Vec<_>>()
            .serialize(serializer)
    }

    pub fn deserialize<'de, D: serde::Deserializer<'de>, V: serde::Deserialize<'de>>(
        deserializer: D,
    ) -> Result<super::HashMap<super::LocalDefId, V>, D::Error> {
        Ok(Vec::deserialize(deserializer)?
            .into_iter()
            .map(|(Helper(k), v)| (k, v))
            .collect())
    }
}

#[cfg(feature = "rustc")]
mod ser_defid_map {
    use serde::{Deserialize, Serialize};

    use flowistry_pdg::rustc_proxies;

    #[derive(Serialize, Deserialize)]
    struct Helper(#[serde(with = "rustc_proxies::DefId")] super::DefId);

    pub fn serialize<S: serde::Serializer, V: serde::Serialize>(
        map: &super::HashMap<super::DefId, V>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        map.iter()
            .map(|(k, v)| (Helper(*k), v))
            .collect::<Vec<_>>()
            .serialize(serializer)
    }

    pub fn deserialize<'de, D: serde::Deserializer<'de>, V: serde::Deserialize<'de>>(
        deserializer: D,
    ) -> Result<super::HashMap<super::DefId, V>, D::Error> {
        Ok(Vec::deserialize(deserializer)?
            .into_iter()
            .map(|(Helper(k), v)| (k, v))
            .collect())
    }
}

/// Exported information from rustc about what sort of object a [`DefId`] points
/// to.
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize, Debug)]
pub struct DefInfo {
    /// Name of the object. Usually the one that a user assigned, but can be
    /// generated in the case of closures and generators
    pub name: Identifier,
    /// Def path to the object
    pub path: Vec<Identifier>,
    /// Kind of object
    pub kind: DefKind,
}

/// Similar to `DefKind` in rustc but *not the same*!
#[derive(
    Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Debug, strum::EnumIs, strum::AsRefStr,
)]
pub enum DefKind {
    Fn,
    Generator,
    Closure,
    Type,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, Eq, Ord, PartialOrd, PartialEq)]
pub struct FunctionCallInfo {
    pub is_inlined: bool,
    #[cfg_attr(feature = "rustc", serde(with = "rustc_proxies::DefId"))]
    pub id: DefId,
}

#[derive(
    Debug, Clone, Copy, Serialize, Deserialize, Eq, Ord, PartialOrd, PartialEq, strum::EnumIs,
)]
pub enum InstructionInfo {
    Statement,
    FunctionCall(FunctionCallInfo),
    Terminator,
    Start,
    Return,
}

impl InstructionInfo {
    pub fn as_function_call(self) -> Option<FunctionCallInfo> {
        match self {
            InstructionInfo::FunctionCall(d) => Some(d),
            _ => None,
        }
    }
}

/// The annotated program dependence graph.
#[derive(Serialize, Deserialize, Debug)]
pub struct ProgramDescription {
    #[cfg_attr(feature = "rustc", serde(with = "ser_localdefid_map"))]
    #[cfg_attr(not(feature = "rustc"), serde(with = "serde_map_via_vec"))]
    /// Mapping from function names to dependencies within the function.
    pub controllers: HashMap<Endpoint, SPDG>,

    #[cfg_attr(not(feature = "rustc"), serde(with = "serde_map_via_vec"))]
    #[cfg_attr(feature = "rustc", serde(with = "ser_defid_map"))]
    pub type_info: HashMap<TypeId, TypeDescription>,

    #[serde(with = "serde_map_via_vec")]
    pub instruction_info: HashMap<GlobalLocation, InstructionInfo>,

    #[cfg_attr(not(feature = "rustc"), serde(with = "serde_map_via_vec"))]
    #[cfg_attr(feature = "rustc", serde(with = "ser_defid_map"))]
    /// Metadata about the `DefId`s
    pub def_info: HashMap<DefId, DefInfo>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct TypeDescription {
    pub rendering: String,
    #[cfg_attr(feature = "rustc", serde(with = "ser_defid_vec"))]
    pub otypes: Vec<TypeId>,
    pub markers: Vec<Identifier>,
}

#[cfg(feature = "rustc")]
mod ser_defid_vec {
    use flowistry_pdg::rustc_proxies;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    #[derive(Serialize, Deserialize)]
    #[repr(transparent)]
    struct DefIdWrap(#[serde(with = "rustc_proxies::DefId")] crate::DefId);

    pub fn serialize<S: Serializer>(
        v: &Vec<crate::DefId>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        unsafe { Vec::<DefIdWrap>::serialize(std::mem::transmute(v), serializer) }
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Vec<crate::DefId>, D::Error> {
        unsafe {
            Ok(std::mem::transmute(Vec::<DefIdWrap>::deserialize(
                deserializer,
            )?))
        }
    }
}

impl ProgramDescription {
    /// Gather all [`DataSource`]s that are mentioned in this program description.
    ///
    /// Essentially just `self.controllers.flat_map(|c| c.keys())`
    pub fn all_sources(&self) -> HashSet<Node> {
        self.controllers
            .values()
            .flat_map(|c| c.all_sources())
            .collect()
    }
    /// Gather all [`DataSource`]s that are mentioned in this program description.
    ///
    /// Essentially just `self.controllers.flat_map(|c| c.keys())`
    pub fn all_sources_with_ctrl(&self) -> HashSet<(Endpoint, Node)> {
        self.controllers
            .iter()
            .flat_map(|(name, c)| c.all_sources().map(|ds| (*name, ds)))
            .collect()
    }
    /// Gather all [`DataSink`]s mentioned in this program description
    ///
    /// Essentially just `self.controllers.flat_map(|c| c.values())`
    pub fn all_sinks(&self) -> HashSet<Node> {
        self.controllers
            .values()
            .flat_map(|ctrl| ctrl.data_sinks())
            .collect()
    }

    /// Gather all [`CallSite`]s that are mentioned in this program description.
    ///
    /// This function is a bit more subtle than [`Self::all_sinks`] and
    /// [`Self::all_sources`] (which are simple maps), because call sites occur
    /// in more places. So this extracts the call sites from sources as well as
    /// sinks.
    pub fn all_call_sites(&self) -> HashSet<CallString> {
        self.controllers
            .values()
            .flat_map(|v| {
                v.graph
                    .edge_weights()
                    .map(|e| e.at)
                    .chain(v.graph.node_weights().map(|n| n.at))
            })
            .collect()
    }
}

/// An identifier for any kind of object (functions, markers, etc.).
///
/// Implemented as an interned string, so identifiers are cheap to reuse.
#[derive(Hash, Eq, PartialEq, Ord, PartialOrd, Clone, Serialize, Deserialize, Copy)]
pub struct Identifier(Intern<String>);

impl Identifier {
    #[cfg(feature = "rustc")]
    pub fn new(s: rustc::span::Symbol) -> Self {
        Self::new_intern(s.as_str())
    }

    /// Returns the underlying string from an identifier.
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// Interns the input string into an identifier.
    ///
    /// Note: this requires locking the global intern arena. See [`internment::Intern`] for details.
    pub fn new_intern(s: &str) -> Self {
        Identifier(Intern::from_ref(s))
    }
}

impl fmt::Debug for Identifier {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Display::fmt(self.0.as_ref(), f)
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        self.0.as_ref().fmt(f)
    }
}

/// Create a hash for this object that is no longer than six hex digits
///
/// The intent for this is to be used as a pre- or postfix to make a non-unique
/// name for the object `T` unique. The [`fmt::Display`] implementation should be
/// used for canonical formatting.
#[derive(Debug, Clone, Copy)]
pub struct ShortHash(u64);

impl ShortHash {
    pub fn new<T: Hash>(t: T) -> Self {
        // Six digits in hex
        Self(hash_pls(t) % 0x1_000_000)
    }
}

impl fmt::Display for ShortHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:06x}", self.0)
    }
}

#[test]
fn short_hash_always_six_digits() {
    assert_eq!(format!("{}", ShortHash(0x0)).len(), 6);
    assert_eq!(format!("{}", ShortHash(0x57110)).len(), 6);
}

/// Calculate a hash for this object
pub fn hash_pls<T: Hash>(t: T) -> u64 {
    use std::hash::Hasher;
    let mut hasher = std::collections::hash_map::DefaultHasher::default();
    t.hash(&mut hasher);
    hasher.finish()
}

pub struct GlobalNodeIter<I: IntoIterGlobalNodes> {
    controller_id: LocalDefId,
    iter: I::Iter,
}

impl<I: IntoIterGlobalNodes> Iterator for GlobalNodeIter<I> {
    type Item = GlobalNode;
    fn next(&mut self) -> Option<Self::Item> {
        Some(GlobalNode {
            controller_id: self.controller_id,
            node: self.iter.next()?,
        })
    }
}

pub trait IntoIterGlobalNodes: Sized + Copy {
    type Iter: Iterator<Item = Node>;
    fn iter_nodes(self) -> Self::Iter;

    fn controller_id(self) -> LocalDefId;

    fn iter_global_nodes(self) -> GlobalNodeIter<Self> {
        GlobalNodeIter {
            controller_id: self.controller_id(),
            iter: self.iter_nodes(),
        }
    }

    /// A convenience method for gathering multiple node(cluster)s together.
    ///
    /// Returns `None` if the controller id's don't match or both iterators are empty.
    fn extended(self, other: impl IntoIterGlobalNodes) -> Option<NodeCluster> {
        if self.controller_id() != other.controller_id() {
            return None;
        }
        Some(NodeCluster::new(
            self.controller_id(),
            self.iter_nodes().chain(other.iter_nodes()).peekable(),
        ))
    }

    fn to_local_cluster(self) -> NodeCluster {
        NodeCluster::new(self.controller_id(), self.iter_nodes())
    }
}

pub type Node = NodeIndex;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct GlobalNode {
    node: Node,
    controller_id: LocalDefId,
}

impl GlobalNode {
    /// Create a new node with no guarantee that it exists in the SPDG of the
    /// controller.
    pub fn unsafe_new(ctrl_id: LocalDefId, index: usize) -> Self {
        GlobalNode {
            controller_id: ctrl_id,
            node: crate::Node::new(index),
        }
    }

    pub fn from_local_node(ctrl_id: LocalDefId, node: Node) -> Self {
        GlobalNode {
            controller_id: ctrl_id,
            node,
        }
    }

    pub fn local_node(self) -> Node {
        self.node
    }

    pub fn controller_id(self) -> LocalDefId {
        self.controller_id
    }
}

impl IntoIterGlobalNodes for GlobalNode {
    type Iter = std::iter::Once<Node>;
    fn iter_nodes(self) -> Self::Iter {
        std::iter::once(self.local_node())
    }

    fn controller_id(self) -> LocalDefId {
        self.controller_id
    }
}

#[derive(Debug, Hash, Clone)]
pub struct NodeCluster {
    controller_id: LocalDefId,
    nodes: Box<[Node]>,
}

pub struct NodeClusterIter<'a> {
    inner: std::slice::Iter<'a, Node>,
}

impl Iterator for NodeClusterIter<'_> {
    type Item = Node;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().copied()
    }
}

impl<'a> IntoIterGlobalNodes for &'a NodeCluster {
    type Iter = NodeClusterIter<'a>;
    fn iter_nodes(self) -> Self::Iter {
        NodeClusterIter {
            inner: self.nodes.iter(),
        }
    }

    fn controller_id(self) -> LocalDefId {
        self.controller_id
    }
}

impl NodeCluster {
    pub fn new(controller_id: LocalDefId, nodes: impl IntoIterator<Item = Node>) -> Self {
        Self {
            controller_id,
            nodes: nodes.into_iter().collect::<Vec<_>>().into(),
        }
    }

    pub fn controller_id(&self) -> LocalDefId {
        self.controller_id
    }

    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct GlobalEdge {
    index: EdgeIndex,
    controller_id: LocalDefId,
}

impl GlobalEdge {
    pub fn controller_id(self) -> LocalDefId {
        self.controller_id
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NodeInfo {
    pub at: CallString,
    pub description: String,
    pub kind: NodeKind,
}

impl Display for NodeInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} @ {} ({})", self.description, self.at, self.kind)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, Copy, strum::EnumIs)]
pub enum NodeKind {
    FormalParameter(u8),
    FormalReturn,
    ActualParameter(TinyBitSet),
    ActualReturn,
    Unspecified,
}

impl Display for NodeKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            NodeKind::FormalParameter(i) => {
                write!(f, "Formal Parameter [{i}]")
            }
            NodeKind::FormalReturn => f.write_str("Formal Return"),
            NodeKind::ActualParameter(p) => {
                write!(f, "Actual Parameters {}", p.display_pretty())
            }
            NodeKind::ActualReturn => f.write_str("Actual Return"),
            NodeKind::Unspecified => f.write_str("Unspecified"),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EdgeInfo {
    pub kind: EdgeKind,
    pub at: CallString,
}

impl Display for EdgeInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} ({})", self.at, self.kind)
    }
}

impl EdgeInfo {
    pub fn is_data(&self) -> bool {
        matches!(self.kind, EdgeKind::Data)
    }

    pub fn is_control(&self) -> bool {
        matches!(self.kind, EdgeKind::Control)
    }
}

#[derive(
    Clone, Debug, Copy, Eq, PartialEq, Deserialize, Serialize, strum::EnumIs, strum::Display,
)]
pub enum EdgeKind {
    Data,
    Control,
}

pub type SPDGImpl = petgraph::Graph<NodeInfo, EdgeInfo>;

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct SPDG {
    pub name: Identifier,
    pub graph: SPDGImpl,
    pub markers: HashMap<Node, Vec<Identifier>>,
    pub arguments: Vec<Node>,
    /// If the return is `()` or `!` then this is `None`
    pub return_: Option<Node>,
    pub type_assigns: HashMap<Node, Types>,
}

#[derive(Clone, Serialize, Deserialize, Debug, Default)]
pub struct Types(#[cfg_attr(feature = "rustc", serde(with = "ser_defid_vec"))] pub Vec<TypeId>);

impl SPDG {
    pub fn node_info(&self, node: Node) -> &NodeInfo {
        self.graph.node_weight(node).unwrap()
    }

    /// Returns an iterator over all the data sinks in the `data_flow` relation.
    pub fn data_sinks(&self) -> impl Iterator<Item = Node> + '_ {
        self.graph
            .edge_references()
            .filter(|e| e.weight().is_data())
            .map(|e| e.target())
            .unique()
    }

    pub fn edges(&self) -> impl Iterator<Item = EdgeReference<'_, EdgeInfo>> + '_ {
        self.graph.edge_references()
    }

    /// Gather all [`Node`]s that are mentioned in this controller including data and control flow.
    pub fn all_sources(&self) -> impl Iterator<Item = Node> + '_ {
        self.graph.node_identifiers().map(Into::into)
    }

    pub fn dump_dot(&self, mut out: impl std::io::Write) -> std::io::Result<()> {
        use petgraph::dot::Dot;
        let dot = Dot::with_config(&self.graph, &[]);
        write!(out, "{dot}")
    }
}

/// A structure with a [`Display`] implementation that shows information about a
/// node index in a given graph.
#[derive(Clone)]
pub struct DisplayNode<'a> {
    node: NodeIndex,
    graph: &'a SPDG,
    detailed: bool,
}

impl<'a> DisplayNode<'a> {
    pub fn pretty(node: NodeIndex, graph: &'a SPDG) -> Self {
        Self {
            node,
            graph,
            detailed: true,
        }
    }

    pub fn simple(node: NodeIndex, graph: &'a SPDG) -> Self {
        Self {
            node,
            graph,
            detailed: false,
        }
    }
}

impl<'a> Display for DisplayNode<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let weight = self.graph.graph.node_weight(self.node).unwrap();
        if self.detailed {
            write!(
                f,
                "{{{}}} ({}) {} @ {}",
                self.node.index(),
                weight.kind,
                weight.description,
                weight.at
            )
        } else {
            write!(f, "{{{}}} {}", self.node.index(), weight.description)
        }
    }
}
