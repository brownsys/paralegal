//! The representation of the PDG.

use std::{
    fmt::{self, Display},
    hash::Hash,
    path::Path,
};

use flowistry_pdg::{CallString, Constant, RichLocation};
use internment::Intern;
use petgraph::{dot, graph::DiGraph, visit::IntoNodeReferences};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{self, Body, HasLocalDecls, Local, LocalDecl, LocalDecls, Location, Place},
    ty::{self, GenericArgsRef, Instance, TyCtxt},
};
use rustc_span::Span;
use rustc_utils::PlaceExt;

pub use flowistry_pdg::{SourceUse, TargetUse};

/// Usually a location in a MIR body but can also cross "one hop" into a called function.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct OneHopLocation {
    /// The point in the execution of the program.
    pub location: RichLocation,
    /// If this is actually a place in a called function, then this refes to the
    /// function that was called and whether it refers to the start or end
    /// location in that function. In that case `at` refers to the location at
    /// which the function call occurs in the parent.
    pub in_child: Option<(DefId, bool)>,
}

impl fmt::Display for OneHopLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.location)?;
        if let Some((_, is_start)) = self.in_child {
            write!(f, " -> {}", if is_start { "start" } else { "end" })?;
        }
        Ok(())
    }
}

impl From<RichLocation> for OneHopLocation {
    fn from(location: RichLocation) -> Self {
        OneHopLocation {
            location,
            in_child: None,
        }
    }
}

impl From<Location> for OneHopLocation {
    fn from(at: Location) -> Self {
        OneHopLocation {
            location: RichLocation::Location(at),
            in_child: None,
        }
    }
}

impl<T: Copy> From<&'_ T> for OneHopLocation
where
    OneHopLocation: From<T>,
{
    fn from(at: &'_ T) -> Self {
        OneHopLocation::from(*at)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DepNodePlaceKind<'tcx> {
    pub place: Place<'tcx>,
    /// Pretty representation of the place.
    /// This is cached as an interned string on [`DepNode`] because to compute it later,
    /// we would have to regenerate the entire monomorphized body for a given place.
    pub(crate) place_pretty: Option<Intern<String>>,
    /// Does the PDG track subplaces of this place?
    pub is_split: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DepNodeKind<'tcx> {
    Place(DepNodePlaceKind<'tcx>),
    Const(Constant),
}

/// A node in the program dependency graph.
///
/// Represents a place at a particular call-string.
/// The place is in the body of the root of the call-string.
#[derive(Clone, Debug)]
pub struct DepNode<'tcx, Loc> {
    pub kind: DepNodeKind<'tcx>,

    /// Location of the place in the program.
    pub at: Loc,
}

impl<Loc: PartialEq> PartialEq for DepNode<'_, Loc> {
    fn eq(&self, other: &Self) -> bool {
        // Using an explicit match here with all fields, so that should new
        // fields be added we remember to check whether they need to be included
        // here.
        let Self { at, kind } = self;
        match (kind, &other.kind) {
            (
                DepNodeKind::Place(DepNodePlaceKind {
                    place,
                    place_pretty: _,
                    span,
                    is_split,
                }),
                DepNodeKind::Place(other_kind),
            ) => {
                let eq = (place, at).eq(&(&other_kind.place, &other.at));
                if eq {
                    debug_assert_eq!(span, &other_kind.span);
                    debug_assert_eq!(is_split, &other_kind.is_split);
                }
                eq
            }
            (k1, k2) => at == &other.at && k1 == k2,
        }
    }
}

impl<Loc: Eq> Eq for DepNode<'_, Loc> {}

impl<Loc: Hash> Hash for DepNode<'_, Loc> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Using an explicit match here with all fields, so that should new
        // fields be added we remember to check whether they need to be included
        // here.
        let place_or_const = match &self.kind {
            DepNodeKind::Const(c) => Ok(c),
            DepNodeKind::Place(p) => Err(p.place),
        };
        (place_or_const, &self.at).hash(state)
    }
}

impl<'tcx> DepNode<'tcx, OneHopLocation> {
    /// Constructs a new [`DepNode`].
    ///
    /// The `tcx` and `body` arguments are used to precompute a pretty string
    /// representation of the [`DepNode`].
    pub fn for_place(
        place: Place<'tcx>,
        at: OneHopLocation,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        context: DefId,
        is_split: bool,
    ) -> Self {
        let span = match at.location {
            RichLocation::Location(loc) => {
                let expanded_span = body
                    .stmt_at(loc)
                    .either(|s| s.source_info.span, |t| t.source_info.span);
                tcx.sess.source_map().stmt_span(expanded_span, body.span)
            }
            RichLocation::Start | RichLocation::End => tcx.def_span(context),
        };
        DepNode {
            kind: DepNodeKind::Place(DepNodePlaceKind {
                place,
                place_pretty: place.to_string(tcx, body).map(Intern::new),
                span,
                is_split,
            }),
            at,
        }
    }
}

impl<'a, Loc> DepNode<'a, Loc> {
    /// Returns a pretty string representation of the place, if one exists.
    pub fn place_pretty(&self) -> Option<&str> {
        if let DepNodeKind::Place(p) = &self.kind {
            p.place_pretty.map(|s| s.as_ref().as_str())
        } else {
            None
        }
    }

    pub fn map_at<'b, Loc2, F: FnOnce(&'b Loc) -> Loc2>(&'b self, f: F) -> DepNode<'a, Loc2> {
        DepNode {
            kind: self.kind.clone(),
            at: f(&self.at),
        }
    }

    pub fn make_descriptor(&self) -> PlaceOrConst<'a> {
        match &self.kind {
            DepNodeKind::Const(c) => PlaceOrConst::Const(*c),
            DepNodeKind::Place(p) => PlaceOrConst::Place(p.place),
        }
    }

    fn display_place(&self) -> DisplayNodeKind<'a> {
        DisplayNodeKind(self.make_descriptor())
    }

    pub fn place(&self) -> Option<Place<'a>> {
        if let DepNodeKind::Place(DepNodePlaceKind { place, .. }) = self.kind {
            Some(place)
        } else {
            None
        }
    }
}

impl<Loc: fmt::Display> fmt::Display for DepNode<'_, Loc> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            DepNodeKind::Place(p) => match self.place_pretty() {
                Some(s) => s.fmt(f)?,
                None => write!(f, "{:?}", p.place)?,
            },
            DepNodeKind::Const(c) => write!(f, "{c}")?,
        }
        write!(f, " @ {}", self.at)
    }
}

pub struct DisplayNodeKind<'tcx>(PlaceOrConst<'tcx>);

impl std::fmt::Display for DisplayNodeKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            PlaceOrConst::Place(p) => write!(f, "{:?}", p),
            PlaceOrConst::Const(c) => write!(f, "{c}"),
        }
    }
}

impl std::fmt::Debug for DisplayNodeKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

/// A kind of edge in the program dependence graph.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum DepEdgeKind {
    /// X is control-dependent on Y if the value of Y influences the execution
    /// of statements that affect the value of X.
    Control,

    /// X is data-dependent on Y if the value of Y is an input to statements that affect
    /// the value of X.
    Data,
}

/// An edge in the program dependence graph.
///
/// Represents an operation that induces a dependency between places.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DepEdge<Loc> {
    /// Either data or control.
    pub kind: DepEdgeKind,

    /// The location of the operation.
    pub at: Loc,

    pub source_use: SourceUse,

    pub target_use: TargetUse,
}

impl<Loc> DepEdge<Loc> {
    /// Constructs a data edge.
    pub fn data(at: Loc, source_use: SourceUse, target_use: TargetUse) -> Self {
        DepEdge {
            kind: DepEdgeKind::Data,
            at,
            source_use,
            target_use,
        }
    }

    /// Constructs a control edge.
    pub fn control(at: Loc, source_use: SourceUse, target_use: TargetUse) -> Self {
        DepEdge {
            kind: DepEdgeKind::Control,
            at,
            source_use,
            target_use,
        }
    }

    pub fn is_control(&self) -> bool {
        self.kind == DepEdgeKind::Control
    }
    pub fn is_data(&self) -> bool {
        self.kind == DepEdgeKind::Data
    }
}

impl<Loc> DepEdge<Loc> {
    pub fn map_at<'a, Loc2, F: FnOnce(&'a Loc) -> Loc2>(&'a self, f: F) -> DepEdge<Loc2> {
        DepEdge {
            kind: self.kind,
            at: f(&self.at),
            source_use: self.source_use,
            target_use: self.target_use,
        }
    }
}

impl<Loc: fmt::Display> fmt::Display for DepEdge<Loc> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}\n@ {}", self.kind, self.at)
    }
}

/// The top-level PDG.
#[derive(Debug)]
pub struct DepGraph<'tcx> {
    /// The petgraph representation of the PDG.
    pub graph: DiGraph<DepNode<'tcx, CallString>, DepEdge<CallString>>,
}

impl Clone for DepGraph<'_> {
    fn clone(&self) -> Self {
        DepGraph {
            graph: self.graph.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.graph.clone_from(&source.graph);
    }
}

impl<'tcx> DepGraph<'tcx> {
    /// Constructs a new [`DepGraph`].
    pub fn new(graph: DiGraph<DepNode<'tcx, CallString>, DepEdge<CallString>>) -> Self {
        Self { graph }
    }
}

impl DepGraph<'_> {
    /// Generates a graphviz visualization of the PDG and saves it to `path`.
    pub fn generate_graphviz(&self, path: impl AsRef<Path>) -> anyhow::Result<()> {
        let graph_dot = format!(
            "{}",
            dot::Dot::with_attr_getters(
                &self.graph,
                &[],
                &|_, _| "fontname=\"Courier New\"".to_string(),
                &|_, (_, _)| "fontname=\"Courier New\",shape=box".to_string(),
            )
        );
        rustc_utils::mir::body::run_dot(path.as_ref(), &graph_dot.into_bytes())
    }
}

pub type Node = petgraph::graph::NodeIndex;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum PlaceOrConst<'tcx> {
    Place(Place<'tcx>),
    Const(Constant),
}

impl<'tcx> From<Place<'tcx>> for PlaceOrConst<'tcx> {
    fn from(value: Place<'tcx>) -> Self {
        Self::Place(value)
    }
}

impl<'tcx> From<Constant> for PlaceOrConst<'tcx> {
    fn from(value: Constant) -> Self {
        Self::Const(value)
    }
}

impl<'tcx, T: Copy + Into<PlaceOrConst<'tcx>>> From<&'_ T> for PlaceOrConst<'tcx> {
    fn from(value: &'_ T) -> Self {
        (*value).into()
    }
}

impl<'tcx> PlaceOrConst<'tcx> {
    pub fn try_from_operand(
        tcx: ty::TyCtxt<'tcx>,
        operand: mir::Operand<'tcx>,
    ) -> Result<Self, ConstConversionError<'tcx>> {
        Ok(match operand {
            mir::Operand::Copy(place) => Self::Place(place),
            mir::Operand::Move(place) => Self::Place(place),
            mir::Operand::Constant(constant) => {
                Self::Const(constant_from_const(tcx, &constant.const_)?)
            }
        })
    }
}

#[derive(Debug, Clone)]
enum ConstConversionError<'tcx> {
    UnsupportedConstType(mir::Const<'tcx>),
    Integer128NotSupported { signed: bool },
}

pub fn constant_from_const<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    c: &mir::Const<'tcx>,
) -> Result<Constant, ConstConversionError<'tcx>> {
    match c {
        mir::Const::Val(val, ty) => constant_from_const_value(tcx, *ty, val),
        _ => Err(ConstConversionError::UnsupportedConstType(c.clone())),
    }
}

fn constant_from_const_value<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    ct: &mir::ConstValue<'tcx>,
) -> Result<Constant, ConstConversionError<'tcx>> {
    // largely from rustc_middle/mir/pretty.rs.html#1952-1962
    match (ct, ty.kind()) {
        (_, ty::Ref(_, inner_ty, _)) if matches!(inner_ty.kind(), ty::Str) => {
            if let Some(data) = ct.try_get_slice_bytes_for_diagnostics(tcx) {
                return Ok(Constant::String(Intern::from_ref(
                    String::from_utf8_lossy(data).as_ref(),
                )));
            }
            ()
        }
        (mir::ConstValue::Scalar(mir::interpret::Scalar::Int(int)), tyk) => match tyk {
            ty::Bool => return Ok(Constant::Bool(int.try_to_bool().unwrap())),
            // Skipping floats for now.
            // ty::Float(fty) => Self::Float(match fty {
            //     ty::FloatTy::F16 => int.to_f16() as f64,
            //     ty::FloatTy::F32 => int.to_f32() as f64,
            //     ty::FloatTy::F64 => int.to_f64() as f64,
            // }),
            ty::Int(ity) => {
                return Ok(Constant::Int(match ity {
                    ty::IntTy::I8 => int.to_u8() as i64,
                    ty::IntTy::I16 => int.to_u16() as i64,
                    ty::IntTy::I32 => int.to_u32() as i64,
                    ty::IntTy::I64 => int.to_u64() as i64,
                    ty::IntTy::Isize => int.to_target_isize(tcx) as i64,
                    ty::IntTy::I128 => {
                        return Err(ConstConversionError::Integer128NotSupported { signed: true })
                    }
                }))
            }
            ty::Uint(uty) => {
                return Ok(Constant::Uint(match uty {
                    ty::UintTy::U8 => int.to_u8() as u64,
                    ty::UintTy::U16 => int.to_u16() as u64,
                    ty::UintTy::U32 => int.to_u32() as u64,
                    ty::UintTy::U64 => int.to_u64() as u64,
                    ty::UintTy::Usize => int.to_target_usize(tcx) as u64,
                    ty::UintTy::U128 => {
                        return Err(ConstConversionError::Integer128NotSupported { signed: false })
                    }
                }))
            }
            _ => (),
        },
        _ => (),
    }
    Err(ConstConversionError::UnsupportedConstType(mir::Const::Val(
        ct.clone(),
        ty,
    )))
}

#[derive(Debug, Clone)]
pub struct PartialGraph<'tcx, K> {
    node_mapping: FxHashMap<(PlaceOrConst<'tcx>, OneHopLocation), Node>,
    graph: petgraph::Graph<DepNode<'tcx, OneHopLocation>, DepEdge<OneHopLocation>>,
    pub(crate) def_id: DefId,
    arg_count: usize,
    pub(crate) generics: GenericArgsRef<'tcx>,
    local_decls: IndexVec<Local, LocalDecl<'tcx>>,
    pub(crate) k: K,
    pub(crate) inlined_calls: Vec<(
        Location,
        Instance<'tcx>,
        K,
        Vec<GraphConnectionPoint<'tcx, OneHopLocation>>,
    )>,
}

pub type GraphConnectionPoint<'tcx, Loc> = (Node, DepEdge<Loc>);

impl<'tcx, K> HasLocalDecls<'tcx> for PartialGraph<'tcx, K> {
    fn local_decls(&self) -> &LocalDecls<'tcx> {
        &self.local_decls
    }
}

impl<'tcx, K> PartialGraph<'tcx, K> {
    pub(crate) fn new(
        generics: GenericArgsRef<'tcx>,
        def_id: DefId,
        arg_count: usize,
        local_decls: &LocalDecls<'tcx>,
        k: K,
    ) -> Self {
        Self {
            node_mapping: Default::default(),
            graph: petgraph::Graph::new(),
            generics,
            def_id,
            arg_count,
            local_decls: local_decls.to_owned(),
            inlined_calls: Default::default(),
            k,
        }
    }

    pub fn def_id(&self) -> DefId {
        self.def_id
    }

    pub(crate) fn insert_node(&mut self, node: DepNode<'tcx, OneHopLocation>) -> Node {
        self.get_or_construct_node(node.make_descriptor(), node.at.clone(), || node)
    }

    pub fn get_place_node(&self, place: Place<'tcx>, at: OneHopLocation) -> Option<Node> {
        self.get_node(place.into(), at)
    }

    pub fn get_node(&self, place: PlaceOrConst<'tcx>, at: OneHopLocation) -> Option<Node> {
        self.node_mapping.get(&(place, at)).copied()
    }

    pub(crate) fn get_or_construct_node(
        &mut self,
        place: PlaceOrConst<'tcx>,
        at: OneHopLocation,
        construct: impl FnOnce() -> DepNode<'tcx, OneHopLocation>,
    ) -> Node {
        if let Some(node) = self.get_node(place, at.clone()) {
            node
        } else {
            let node = construct();
            let idx = self.graph.add_node(node);
            self.node_mapping.insert((place, at), idx);
            idx
        }
    }

    pub(crate) fn insert_edge(
        &mut self,
        source: Node,
        target: Node,
        edge: DepEdge<OneHopLocation>,
    ) {
        if let Some(prior) = self.graph.find_edge(source, target) {
            let e = self.graph.edge_weight(prior).unwrap();
            assert_eq!(
                e,
                &edge,
                "Edge {} -> {} already exists in {:?}",
                self.node_props(source).display_place(),
                self.node_props(target).display_place(),
                self.def_id
            );
        } else {
            self.graph.add_edge(source, target, edge);
        }
    }

    pub fn iter_nodes(
        &self,
    ) -> impl Iterator<Item = (Node, &DepNode<'tcx, OneHopLocation>)> + Clone {
        self.graph.node_references()
    }

    pub fn iter_edges<'a>(
        &'a self,
    ) -> impl Iterator<Item = (Node, Node, &'a DepEdge<OneHopLocation>)> + use<'tcx, 'a, K> {
        use petgraph::visit::EdgeRef;
        self.graph
            .edge_references()
            .map(|r| (r.source(), r.target(), r.weight()))
    }

    pub fn node_props(&self, node: Node) -> &DepNode<'tcx, OneHopLocation> {
        self.graph.node_weight(node).unwrap()
    }

    /// Returns the set of source places that the parent can access (write to)
    pub(crate) fn parentable_srcs<'a>(&'a self) -> FxHashSet<(DepNode<'tcx, bool>, Option<u8>)> {
        self.iter_edges()
            .filter(|&(n, _, _)| self.node_props(n).at.location.is_start())
            .map(|(n, _, _)| {
                let n = self.node_props(n);
                n.map_at(|_| {
                    assert!(n.at.in_child.is_none());
                    true
                })
            })
            .filter_map(move |a| {
                let as_arg = as_arg(&a, self.arg_count)?;
                Some((a, as_arg))
            })
            .collect()
    }

    /// Returns the set of destination places that the parent can access (read
    /// from)
    pub(crate) fn parentable_dsts<'a>(&'a self) -> FxHashSet<(DepNode<'tcx, bool>, Option<u8>)> {
        self.iter_nodes()
            .map(|(_, n)| n)
            .filter(|n| n.at.location.is_end())
            .map(|n| {
                assert!(n.at.in_child.is_none());
                n.map_at(|_| false)
            })
            .filter_map(move |a| {
                let arg = as_arg(&a, self.arg_count)?;
                Some((a, arg))
            })
            .collect()
    }

    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }

    pub fn raw(&self) -> &petgraph::Graph<DepNode<'tcx, OneHopLocation>, DepEdge<OneHopLocation>> {
        &self.graph
    }
}

fn as_arg<Loc>(node: &DepNode<'_, Loc>, arg_count: usize) -> Option<Option<u8>> {
    let DepNodeKind::Place(node) = &node.kind else {
        return None;
    };
    let local = node.place.local.as_usize();
    if node.place.local == rustc_middle::mir::RETURN_PLACE {
        Some(None)
    } else if local > 0 && (local - 1) < arg_count {
        Some(Some(node.place.local.as_u32() as u8 - 1))
    } else {
        None
    }
}
