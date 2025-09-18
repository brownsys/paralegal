//! The representation of the PDG.

use std::{
    fmt::{self},
    hash::Hash,
    path::Path,
};

use flowistry_pdg::{CallString, RichLocation};
use internment::Intern;
use petgraph::{dot, graph::DiGraph};

use rustc_hash::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{Body, HasLocalDecls, Local, LocalDecl, LocalDecls, Location, Place},
    ty::{GenericArgsRef, Instance, TyCtxt},
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

/// A node in the program dependency graph.
///
/// Represents a place at a particular call-string.
/// The place is in the body of the root of the call-string.
#[derive(Clone, Debug)]
pub struct DepNode<'tcx, Loc> {
    /// A place in memory in a particular body.
    pub place: Place<'tcx>,

    /// Location of the place in the program.
    pub at: Loc,

    /// Pretty representation of the place.
    /// This is cached as an interned string on [`DepNode`] because to compute it later,
    /// we would have to regenerate the entire monomorphized body for a given place.
    pub(crate) place_pretty: Option<Intern<String>>,
    /// Does the PDG track subplaces of this place?
    pub is_split: bool,
    pub span: Span,
}

impl<Loc: PartialEq> PartialEq for DepNode<'_, Loc> {
    fn eq(&self, other: &Self) -> bool {
        // Using an explicit match here with all fields, so that should new
        // fields be added we remember to check whether they need to be included
        // here.
        let Self {
            place,
            at,
            place_pretty: _,
            span,
            is_split,
        } = self;
        let eq = (place, at).eq(&(&other.place, &other.at));
        if eq {
            debug_assert_eq!(span, &other.span);
            debug_assert_eq!(is_split, &other.is_split);
        }
        eq
    }
}

impl<Loc: Eq> Eq for DepNode<'_, Loc> {}

impl<Loc: Hash> Hash for DepNode<'_, Loc> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Using an explicit match here with all fields, so that should new
        // fields be added we remember to check whether they need to be included
        // here.
        let Self {
            place,
            at,
            place_pretty: _,
            span: _,
            is_split: _,
        } = self;
        (place, at).hash(state)
    }
}

impl<'tcx> DepNode<'tcx, OneHopLocation> {
    /// Constructs a new [`DepNode`].
    ///
    /// The `tcx` and `body` arguments are used to precompute a pretty string
    /// representation of the [`DepNode`].
    pub fn new(
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
            place,
            at,
            place_pretty: place.to_string(tcx, body).map(Intern::new),
            span,
            is_split,
        }
    }
}

impl<'a, Loc> DepNode<'a, Loc> {
    /// Returns a pretty string representation of the place, if one exists.
    pub fn place_pretty(&self) -> Option<&str> {
        self.place_pretty.map(|s| s.as_ref().as_str())
    }

    pub fn map_at<'b, Loc2, F: FnOnce(&'b Loc) -> Loc2>(&'b self, f: F) -> DepNode<'a, Loc2> {
        DepNode {
            place: self.place,
            at: f(&self.at),
            place_pretty: self.place_pretty,
            span: self.span,
            is_split: self.is_split,
        }
    }
}

impl<Loc: fmt::Display> fmt::Display for DepNode<'_, Loc> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.place_pretty() {
            Some(s) => s.fmt(f)?,
            None => write!(f, "{:?}", self.place)?,
        };
        write!(f, " @ {}", self.at)
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

#[derive(Debug, Clone)]
pub struct PartialGraph<'tcx, K> {
    pub(crate) nodes: FxHashSet<DepNode<'tcx, OneHopLocation>>,
    pub(crate) edges: FxHashSet<(
        DepNode<'tcx, OneHopLocation>,
        DepNode<'tcx, OneHopLocation>,
        DepEdge<OneHopLocation>,
    )>,
    pub(crate) generics: GenericArgsRef<'tcx>,
    pub(crate) def_id: DefId,
    arg_count: usize,
    local_decls: IndexVec<Local, LocalDecl<'tcx>>,
    pub(crate) k: K,
    pub(crate) inlined_calls: Vec<(Location, Instance<'tcx>, K, Vec<GraphConnectionPoint<'tcx>>)>,
}

type GraphConnectionPoint<'tcx> = (DepNode<'tcx, OneHopLocation>, DepEdge<OneHopLocation>);

impl<'tcx, K> HasLocalDecls<'tcx> for PartialGraph<'tcx, K> {
    fn local_decls(&self) -> &LocalDecls<'tcx> {
        &self.local_decls
    }
}

impl<'tcx, K> PartialGraph<'tcx, K> {
    pub fn new(
        generics: GenericArgsRef<'tcx>,
        def_id: DefId,
        arg_count: usize,
        local_decls: &LocalDecls<'tcx>,
        k: K,
    ) -> Self {
        Self {
            nodes: Default::default(),
            edges: Default::default(),
            generics,
            def_id,
            arg_count,
            local_decls: local_decls.to_owned(),
            inlined_calls: Default::default(),
            k,
        }
    }

    pub fn iter_nodes(&self) -> impl Iterator<Item = &DepNode<'tcx, OneHopLocation>> + Clone {
        self.nodes.iter()
    }

    pub fn iter_edges(
        &self,
    ) -> impl Iterator<
        Item = &(
            DepNode<'tcx, OneHopLocation>,
            DepNode<'tcx, OneHopLocation>,
            DepEdge<OneHopLocation>,
        ),
    > {
        self.edges.iter()
    }

    /// Returns the set of source places that the parent can access (write to)
    pub(crate) fn parentable_srcs<'a>(&'a self) -> FxHashSet<(DepNode<'tcx, bool>, Option<u8>)> {
        self.edges
            .iter()
            .filter(|&(n, _, _)| n.at.location.is_start())
            .map(|(n, _, _)| {
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
        self.edges
            .iter()
            .filter(|&(_, n, _)| n.at.location.is_end())
            .map(|(_, n, _)| {
                assert!(n.at.in_child.is_none());
                n.map_at(|_| false)
            })
            .filter_map(move |a| {
                let arg = as_arg(&a, self.arg_count)?;
                Some((a, arg))
            })
            .collect()
    }
}

fn as_arg<Loc>(node: &DepNode<'_, Loc>, arg_count: usize) -> Option<Option<u8>> {
    let local = node.place.local.as_usize();
    if node.place.local == rustc_middle::mir::RETURN_PLACE {
        Some(None)
    } else if local > 0 && (local - 1) < arg_count {
        Some(Some(node.place.local.as_u32() as u8 - 1))
    } else {
        None
    }
}
