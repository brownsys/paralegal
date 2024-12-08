//! This crate defines the program dependence graph (PDG) generated by Paralegal.
//!
//! The top-level type is [`ProgramDescription`]. This type references multiple
//! types defined within the Rust compiler such as MIR locations. To avoid requiring
//! a `rustc_private` dependency on paralegal_spdg clients, we provide proxies in the
//! [`rustc_proxies`] module for all Rustc types within the PDG.

#![cfg_attr(feature = "rustc", feature(rustc_private))]
#![warn(missing_docs)]

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

#[cfg(feature = "rustc")]
extern crate rustc_macros;
#[cfg(feature = "rustc")]
extern crate rustc_serialize;

extern crate strum;

pub use flowistry_pdg::*;

pub mod dot;
pub mod ser;
mod tiny_bitset;
pub mod traverse;
pub mod utils;

use internment::Intern;
use itertools::Itertools;
use rustc_portable::DefId;
use serde::{Deserialize, Serialize};
use std::time::Duration;
use std::{fmt, hash::Hash, path::PathBuf};
use utils::write_sep;

use utils::serde_map_via_vec;

pub use crate::tiny_bitset::pretty as tiny_bitset_pretty;
pub use crate::tiny_bitset::TinyBitSet;
use flowistry_pdg::rustc_portable::LocalDefId;
use petgraph::graph::{EdgeIndex, EdgeReference, NodeIndex};
use petgraph::prelude::EdgeRef;
use petgraph::visit::IntoNodeIdentifiers;
pub use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};

/// The types of identifiers that identify an entrypoint
pub type Endpoint = DefId;
/// Identifiers for types
pub type TypeId = DefId;
/// Identifiers for functions
pub type Function = Identifier;

/// Name of the file used for emitting the serialized
/// [`ProgramDescription`].
pub const FLOW_GRAPH_OUT_NAME: &str = "flow-graph.o";

/// Extension for output files containing statistics of the analzyer run.
pub const STAT_FILE_EXT: &str = "stat.json";

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

/// A marker annotation and its refinements.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Serialize, Deserialize)]
pub struct MarkerAnnotation {
    /// The (unchanged) name of the marker as provided by the user
    pub marker: Identifier,
    /// The annotation should apply to the return value
    pub on_return: bool,
    /// The annotation should apply to these arguments
    pub on_argument: TinyBitSet,
}

impl MarkerAnnotation {
    /// Get the refinements on arguments
    pub fn on_argument(&self, arg: u16) -> bool {
        self.on_argument.contains(arg as u32).unwrap_or(false)
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
    pub path: Box<[Identifier]>,
    /// Kind of object
    pub kind: DefKind,
    /// Information about the span
    pub src_info: Span,
    /// Marker annotations on this item
    pub markers: Box<[MarkerAnnotation]>,
}

/// Provides a way to format rust paths
pub struct DisplayPath<'a>(&'a [Identifier]);

impl Display for DisplayPath<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write_sep(f, "::", self.0, Display::fmt)
    }
}

impl<'a> From<&'a [Identifier]> for DisplayPath<'a> {
    fn from(value: &'a [Identifier]) -> Self {
        Self(value)
    }
}

impl<'a> From<&'a Box<[Identifier]>> for DisplayPath<'a> {
    fn from(value: &'a Box<[Identifier]>) -> Self {
        value.as_ref().into()
    }
}

/// Similar to `DefKind` in rustc but *not the same*!
#[derive(
    Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Debug, strum::EnumIs, strum::AsRefStr,
)]
pub enum DefKind {
    /// A regular function object
    Fn,
    /// The function corresponding to a generator
    Generator,
    /// The function corresponding to a closure
    Closure,
    /// A type
    Type,
}

/// An interned [`SourceFileInfo`]
#[derive(Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Debug, Hash, PartialOrd, Ord)]
pub struct SourceFile(Intern<SourceFileInfo>);

impl std::ops::Deref for SourceFile {
    type Target = SourceFileInfo;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Information about a source file
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize, Debug, Hash, PartialOrd, Ord)]
pub struct SourceFileInfo {
    /// Printable location of the source code file - either an absolute path to library source code
    /// or a path relative to within the compiled crate (e.g. `src/...`)
    pub file_path: String,
    /// Absolute path to source code file
    pub abs_file_path: PathBuf,
}

impl SourceFileInfo {
    /// Intern the source file
    pub fn intern(self) -> SourceFile {
        SourceFile(Intern::new(self))
    }
}

/// A "point" within a source file. Used to compose and compare spans.
///
/// NOTE: The ordering of this type must be such that if point "a" is earlier in
/// the file than "b", then "a" < "b".
#[derive(Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Debug, PartialOrd, Ord, Hash)]
pub struct SpanCoord {
    /// Line in the source file
    pub line: u32,
    /// Column of the line
    pub col: u32,
}

/// Encodes a source code location
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize, Debug, PartialOrd, Ord, Hash)]
pub struct Span {
    /// Which file this comes from
    pub source_file: SourceFile,
    /// Starting coordinates of the span
    pub start: SpanCoord,
    /// Ending coordinates of the span,
    pub end: SpanCoord,
}

impl Span {
    /// Is `other` completely contained within `self`
    pub fn contains(&self, other: &Self) -> bool {
        self.source_file == other.source_file && self.start <= other.start && self.end >= other.end
    }

    /// How many lines this span spans
    pub fn line_len(&self) -> u32 {
        self.end.line - self.start.line + 1
    }
}

/// Metadata on a function call.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, Eq, Ord, PartialOrd, PartialEq)]
pub struct FunctionCallInfo {
    /// Has this call been inlined
    pub is_inlined: bool,
    /// What is the ID of the item that was called here.
    #[cfg_attr(feature = "rustc", serde(with = "rustc_proxies::DefId"))]
    pub id: DefId,
}

/// The type of instructions we may encounter
#[derive(
    Debug, Clone, Copy, Serialize, Deserialize, Eq, Ord, PartialOrd, PartialEq, strum::EnumIs,
)]
pub enum InstructionKind {
    /// Some type of statement
    Statement,
    /// A function call
    FunctionCall(FunctionCallInfo),
    /// A basic block terminator, usually switchInt
    Terminator,
    /// The beginning of a function
    Start,
    /// The merged exit points of a function
    Return,
}

impl InstructionKind {
    /// If this identifies a function call, return the information inside.
    pub fn as_function_call(self) -> Option<FunctionCallInfo> {
        match self {
            InstructionKind::FunctionCall(d) => Some(d),
            _ => None,
        }
    }
}

/// Information about an instruction represented in the PDG
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InstructionInfo {
    /// Classification of the instruction
    pub kind: InstructionKind,
    /// The source code span
    pub span: Span,
    /// Textual rendering of the MIR
    pub description: Identifier,
}

/// information about each encountered type.
pub type TypeInfoMap = HashMap<TypeId, TypeDescription>;

/// Endpoints with their SPDGs
pub type ControllerMap = HashMap<Endpoint, SPDG>;

#[doc(hidden)]
/// How was a given function handled by the analyzer
#[derive(Serialize, Deserialize, Debug)]
pub enum FunctionHandling {
    /// A PDG was generated
    PDG,
    /// The function was determined not to assign markers and as a result elided.
    Elided,
}

#[doc(hidden)]
pub type AnalyzedSpans = HashMap<DefId, (Span, FunctionHandling)>;

/// The annotated program dependence graph.
#[derive(Serialize, Deserialize, Debug)]
pub struct ProgramDescription {
    /// Entry points we analyzed and their PDGs
    #[cfg_attr(feature = "rustc", serde(with = "ser_defid_map"))]
    #[cfg_attr(not(feature = "rustc"), serde(with = "serde_map_via_vec"))]
    pub controllers: ControllerMap,

    /// Metadata about types
    #[cfg_attr(not(feature = "rustc"), serde(with = "serde_map_via_vec"))]
    #[cfg_attr(feature = "rustc", serde(with = "ser_defid_map"))]
    pub type_info: TypeInfoMap,

    /// Metadata about the instructions that are executed at all program
    /// locations we know about.
    #[serde(with = "serde_map_via_vec")]
    pub instruction_info: HashMap<GlobalLocation, InstructionInfo>,

    #[cfg_attr(not(feature = "rustc"), serde(with = "serde_map_via_vec"))]
    #[cfg_attr(feature = "rustc", serde(with = "ser_defid_map"))]
    /// Metadata about the `DefId`s
    pub def_info: HashMap<DefId, DefInfo>,
    #[doc(hidden)]
    #[cfg_attr(not(feature = "rustc"), serde(with = "serde_map_via_vec"))]
    #[cfg_attr(feature = "rustc", serde(with = "ser_defid_map"))]
    pub analyzed_spans: AnalyzedSpans,
}

/// Statistics about a single run of paralegal-flow
#[derive(Serialize, Deserialize, Debug)]
pub struct AnalyzerStats {
    /// How many marker annotations were found
    pub marker_annotation_count: u32,
    /// Total time used for the last analzyer run
    pub self_time: Duration,
    /// Time spent dumping MIR
    pub dump_time: Duration,
    /// how long the rust typechecker took
    pub tycheck_time: Duration,
    /// How long we spent on dependencies
    pub dep_time: Duration,
    /// How long rustc ran before out plugin executed
    pub rustc_time: Duration,
    /// How long did it take to serialize the graphs
    pub serialization_time: Duration,
    /// The number of functions we produced a PDG for
    pub pdg_functions: u32,
    /// The lines of code corresponding to the functions from
    /// [`Self::dedup_functions`].
    pub pdg_locs: u32,
    /// The number of functions we produced PDGs for or we inspected to check
    /// for markers.
    pub seen_functions: u32,
    /// The lines of code corresponding to the functions from
    /// [`Self::seen_functions`]. This is the sum of all
    /// `analyzed_locs` of the controllers but deduplicated.
    pub seen_locs: u32,
}

/// Metadata about a type
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct TypeDescription {
    /// How rustc would debug print this type
    pub rendering: String,
    /// Aliases
    #[cfg_attr(feature = "rustc", serde(with = "ser_defid_seq"))]
    pub otypes: Box<[TypeId]>,
    /// Attached markers. Guaranteed not to be empty.
    pub markers: Vec<Identifier>,
}

#[cfg(feature = "rustc")]
mod ser_defid_seq {
    use flowistry_pdg::rustc_proxies;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    #[derive(Serialize, Deserialize)]
    #[repr(transparent)]
    struct DefIdWrap(#[serde(with = "rustc_proxies::DefId")] crate::DefId);

    pub fn serialize<S: Serializer>(v: &[crate::DefId], serializer: S) -> Result<S::Ok, S::Error> {
        unsafe { <[DefIdWrap]>::serialize(std::mem::transmute(v), serializer) }
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Box<[crate::DefId]>, D::Error> {
        unsafe {
            Ok(std::mem::transmute(Box::<[DefIdWrap]>::deserialize(
                deserializer,
            )?))
        }
    }
}

impl ProgramDescription {
    /// Gather all data sources that are mentioned in this program description.
    ///
    /// Essentially just `self.controllers.flat_map(|c| c.keys())`
    pub fn all_nodes(&self) -> HashSet<GlobalNode> {
        self.controllers
            .iter()
            .flat_map(|(name, c)| {
                c.all_sources()
                    .map(|ds| GlobalNode::from_local_node(*name, ds))
            })
            .collect()
    }

    /// Gather all [`CallString`]s that are mentioned in this program description.
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

#[cfg(feature = "rustc")]
impl<S: rustc_serialize::Encoder> rustc_serialize::Encodable<S> for Identifier {
    fn encode(&self, s: &mut S) {
        s.emit_str(self.as_str());
    }
}

#[cfg(feature = "rustc")]
impl<D: rustc_serialize::Decoder> rustc_serialize::Decodable<D> for Identifier {
    fn decode(d: &mut D) -> Self {
        Identifier::new_intern(d.read_str())
    }
}

impl Identifier {
    /// Intern a new identifier from a rustc [`rustc::span::Symbol`]
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
    /// Constructor
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

/// Return type of [`IntoIterGlobalNodes::iter_global_nodes`].
pub struct GlobalNodeIter<I: IntoIterGlobalNodes> {
    controller_id: Endpoint,
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

/// This lets us be agnostic whether a primitive (such as `flows_to`) is called
/// with a [`GlobalNode`] or `&NodeCluster`.
///
/// Note that while [`GlobalNode`] implements this trait [`NodeCluster`] *does
/// not do so directly*, but it's reference `&NodeCluster` does.
pub trait IntoIterGlobalNodes: Sized + Copy {
    /// The iterator returned by [`Self::iter_nodes`]
    type Iter: Iterator<Item = Node>;

    /// iterate over the local nodes
    fn iter_nodes(self) -> Self::Iter;

    /// The controller id all of these nodes are located in.
    fn controller_id(self) -> Endpoint;

    /// Iterate all nodes as globally identified one's.
    ///
    /// The invariant of this iterator is that all `controller_id()`s of the
    /// nodes in the iterator is the same as `self.controller_id()`.
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

    /// Collect the iterator into a cluster
    fn to_local_cluster(self) -> NodeCluster {
        NodeCluster::new(self.controller_id(), self.iter_nodes())
    }
}

/// Local nodes in an [`SPDGImpl`]
pub type Node = NodeIndex;

/// A globally identified node in an SPDG
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct GlobalNode {
    node: Node,
    controller_id: Endpoint,
}

impl GlobalNode {
    /// Create a new node with no guarantee that it exists in the SPDG of the
    /// controller.
    pub fn unsafe_new(ctrl_id: Endpoint, index: usize) -> Self {
        GlobalNode {
            controller_id: ctrl_id,
            node: crate::Node::new(index),
        }
    }

    /// Create a new globally identified node by pairing a node local to a
    /// particular SPDG with it's controller id.
    ///
    /// Meant for internal use only.
    pub fn from_local_node(ctrl_id: Endpoint, node: Node) -> Self {
        GlobalNode {
            controller_id: ctrl_id,
            node,
        }
    }

    /// The local node in the SPDG
    pub fn local_node(self) -> Node {
        self.node
    }

    /// The identifier for the SPDG this node is contained in
    pub fn controller_id(self) -> Endpoint {
        self.controller_id
    }
}

impl IntoIterGlobalNodes for GlobalNode {
    type Iter = std::iter::Once<Node>;
    fn iter_nodes(self) -> Self::Iter {
        std::iter::once(self.local_node())
    }

    fn controller_id(self) -> Endpoint {
        self.controller_id
    }
}

/// Collections of nodes in a single controller
pub mod node_cluster {
    use std::ops::Range;

    use crate::{Endpoint, GlobalNode, IntoIterGlobalNodes, Node};

    /// A globally identified set of nodes that are all located in the same
    /// controller.
    ///
    /// Sometimes it is more convenient to think about such a group instead of
    /// individual [`GlobalNode`]s
    #[derive(Debug, Hash, Clone)]
    pub struct NodeCluster {
        controller_id: Endpoint,
        nodes: Box<[Node]>,
    }

    /// Owned iterator of a [`NodeCluster`]
    pub struct IntoIter {
        inner: NodeCluster,
        idx: Range<usize>,
    }

    impl Iterator for IntoIter {
        type Item = GlobalNode;
        fn next(&mut self) -> Option<Self::Item> {
            let idx = self.idx.next()?;
            Some(GlobalNode::from_local_node(
                self.inner.controller_id,
                self.inner.nodes[idx],
            ))
        }
    }

    /// Iterate over a node cluster but yielding [`GlobalNode`]s
    pub struct Iter<'a> {
        inner: std::slice::Iter<'a, Node>,
    }

    impl Iterator for Iter<'_> {
        type Item = Node;
        fn next(&mut self) -> Option<Self::Item> {
            self.inner.next().copied()
        }
    }

    impl<'a> IntoIterGlobalNodes for &'a NodeCluster {
        type Iter = Iter<'a>;
        fn iter_nodes(self) -> Self::Iter {
            self.iter()
        }

        fn controller_id(self) -> Endpoint {
            self.controller_id
        }
    }

    impl IntoIterator for NodeCluster {
        type Item = GlobalNode;
        type IntoIter = IntoIter;
        fn into_iter(self) -> Self::IntoIter {
            IntoIter {
                idx: 0..self.nodes.len(),
                inner: self,
            }
        }
    }

    impl NodeCluster {
        /// Create a new cluster. This for internal use.
        pub fn new(controller_id: Endpoint, nodes: impl IntoIterator<Item = Node>) -> Self {
            Self {
                controller_id,
                nodes: nodes.into_iter().collect::<Vec<_>>().into(),
            }
        }

        /// Iterate nodes borrowing `self`
        pub fn iter(&self) -> Iter<'_> {
            Iter {
                inner: self.nodes.iter(),
            }
        }

        /// Controller that these nodes belong to
        pub fn controller_id(&self) -> Endpoint {
            self.controller_id
        }

        /// Nodes in this cluster
        pub fn nodes(&self) -> &[Node] {
            &self.nodes
        }

        /// Attempt to collect an iterator of nodes into a cluster
        ///
        /// Returns `None` if the iterator was empty or if two nodes did
        /// not have identical controller id's
        pub fn try_from_iter(iter: impl IntoIterator<Item = GlobalNode>) -> Option<Self> {
            let mut it = iter.into_iter();
            let first = it.next()?;
            let ctrl_id = first.controller_id();
            Some(Self {
                controller_id: ctrl_id,
                nodes: std::iter::once(Some(first.local_node()))
                    .chain(it.map(|n| (n.controller_id() == ctrl_id).then_some(n.local_node())))
                    .collect::<Option<Box<_>>>()?,
            })
        }
    }
}

pub use node_cluster::NodeCluster;

/// The global version of an edge that is tied to some specific entrypoint
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct GlobalEdge {
    index: EdgeIndex,
    controller_id: Endpoint,
}

impl GlobalEdge {
    /// The id of the controller that this edge is located in
    pub fn controller_id(self) -> Endpoint {
        self.controller_id
    }
}

/// Node metadata in the [`SPDGImpl`]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NodeInfo {
    /// Location of the node in the call stack
    pub at: CallString,
    /// The debug print of the `mir::Place` that this node represents
    pub description: String,
    /// Span information for this node
    pub span: Span,
}

impl Display for NodeInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} @ {}", self.description, self.at)
    }
}

/// Metadata for an edge in the [`SPDGImpl`]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EdgeInfo {
    /// What type of edge it is
    pub kind: EdgeKind,
    /// Where in the program this edge arises from
    pub at: CallString,

    /// Why the source of this edge is read
    pub source_use: SourceUse,
    /// Why the target of this edge is written
    pub target_use: TargetUse,
}

impl Display for EdgeInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} ({})", self.at, self.kind)
    }
}

impl EdgeInfo {
    /// Same as `self.kind.is_data()`
    pub fn is_data(&self) -> bool {
        matches!(self.kind, EdgeKind::Data)
    }

    /// Same as `self.kind.is_control()`
    pub fn is_control(&self) -> bool {
        matches!(self.kind, EdgeKind::Control)
    }
}

/// The type of an edge
#[derive(
    Clone, Debug, Copy, Eq, PartialEq, Deserialize, Serialize, strum::EnumIs, strum::Display,
)]
pub enum EdgeKind {
    /// The target can read data created by the source
    Data,
    /// The source controls the execution of the target
    Control,
}

/// The graph portion of an [`SPDG`]
pub type SPDGImpl = petgraph::Graph<NodeInfo, EdgeInfo>;

/// A semantic PDG, e.g. a graph plus marker annotations
#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct SPDG {
    /// The identifier of the entry point to this computation
    pub name: Identifier,
    /// The module path to this controller function
    pub path: Box<[Identifier]>,
    /// The id
    #[cfg_attr(feature = "rustc", serde(with = "rustc_proxies::DefId"))]
    pub id: Endpoint,
    /// The PDG
    pub graph: SPDGImpl,
    /// Nodes to which markers are assigned.
    pub markers: HashMap<Node, Box<[Identifier]>>,
    /// The nodes that represent arguments to the entrypoint
    pub arguments: Box<[Node]>,
    /// If the return is `()` or `!` then this is `None`
    pub return_: Box<[Node]>,
    /// Stores the assignment of relevant (e.g. marked) types to nodes. Node
    /// that this contains multiple types for a single node, because it hold
    /// top-level types and subtypes that may be marked.
    pub type_assigns: HashMap<Node, Types>,
    /// Statistics
    pub statistics: SPDGStats,
}

#[derive(Clone, Serialize, Deserialize, Debug, Default)]
/// Statistics about the code that produced an SPDG
pub struct SPDGStats {
    /// The number of unique lines of code we generated a PDG for. This means
    /// MIR bodies without considering monomorphization
    pub unique_locs: u32,
    /// The number of unique functions that became part of the PDG. Corresponds
    /// to [`Self::unique_locs`].
    pub unique_functions: u32,
    /// The number of lines we ran through the PDG construction. This is higher
    /// than unique LoCs, because we need to analyze some functions multiple
    /// times, due to monomorphization and calls tring differences.
    pub analyzed_locs: u32,
    /// Number of functions that correspond to [`Self::analyzed_locs]`
    pub analyzed_functions: u32,
    /// How many times we inlined functions. This will be higher than
    /// [`Self::analyzed_functions`] because sometimes the callee PDG is served
    /// from the cache.
    pub inlinings_performed: u32,
    /// How long it took to create this PDG
    pub construction_time: Duration,
    /// How long it took to calculate markers and otherwise set up the pdg
    pub conversion_time: Duration,
}

/// Holds [`TypeId`]s that were assigned to a node.
#[derive(Clone, Serialize, Deserialize, Debug, Default)]
pub struct Types(#[cfg_attr(feature = "rustc", serde(with = "ser_defid_seq"))] pub Box<[TypeId]>);

impl SPDG {
    /// Retrieve metadata for this node
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

    /// An iterator over all edges in this graph.
    pub fn edges(&self) -> impl Iterator<Item = EdgeReference<'_, EdgeInfo>> + '_ {
        self.graph.edge_references()
    }

    /// Gather all [`Node`]s that are mentioned in this controller including data and control flow.
    pub fn all_sources(&self) -> impl Iterator<Item = Node> + '_ {
        self.graph.node_identifiers().map(Into::into)
    }

    /// Dump this graph in dot format.
    pub fn dump_dot(&self, mut out: impl std::io::Write) -> std::io::Result<()> {
        use petgraph::dot::Dot;
        let dot = Dot::with_config(&self.graph, &[]);
        write!(out, "{dot}")
    }

    /// The arguments of this spdg. The same as the `arguments` field, but
    /// conveniently paired with the controller id
    pub fn arguments(&self) -> NodeCluster {
        NodeCluster::new(self.id, self.arguments.iter().copied())
    }

    /// All types (if any) assigned to this node
    pub fn node_types(&self, node: Node) -> &[TypeId] {
        self.type_assigns.get(&node).map_or(&[], |r| &r.0)
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
    /// Render the node in extended format
    pub fn pretty(node: NodeIndex, graph: &'a SPDG) -> Self {
        Self {
            node,
            graph,
            detailed: true,
        }
    }

    /// Render the node in simple format
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
                "{{{}}} {} @ {}",
                self.node.index(),
                weight.description,
                weight.at
            )
        } else {
            write!(f, "{{{}}} {}", self.node.index(), weight.description)
        }
    }
}
