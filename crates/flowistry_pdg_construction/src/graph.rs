//! The representation of the PDG.

use std::{
    fmt::{self},
    hash::Hash,
    path::Path,
};

use flowistry_pdg::{CallString, GlobalLocation, RichLocation};
use internment::Intern;
use petgraph::{dot, graph::DiGraph};

use rustc_hash::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{Body, HasLocalDecls, Local, LocalDecl, LocalDecls, Place},
    ty::{GenericArgsRef, TyCtxt},
};
use rustc_span::Span;
use rustc_utils::PlaceExt;

pub use flowistry_pdg::{SourceUse, TargetUse};

use super::utils::Captures;

/// A node in the program dependency graph.
///
/// Represents a place at a particular call-string.
/// The place is in the body of the root of the call-string.
#[derive(Clone, Copy, Debug)]
pub struct DepNode<'tcx> {
    /// A place in memory in a particular body.
    pub place: Place<'tcx>,

    /// The point in the execution of the program.
    pub at: CallString,

    /// Pretty representation of the place.
    /// This is cached as an interned string on [`DepNode`] because to compute it later,
    /// we would have to regenerate the entire monomorphized body for a given place.
    pub(crate) place_pretty: Option<Intern<String>>,
    /// Does the PDG track subplaces of this place?
    pub is_split: bool,
    pub span: Span,
}

impl PartialEq for DepNode<'_> {
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
        } = *self;
        let eq = (place, at).eq(&(other.place, other.at));
        if eq {
            debug_assert_eq!(span, other.span);
            debug_assert_eq!(is_split, other.is_split);
        }
        eq
    }
}

impl Eq for DepNode<'_> {}

impl Hash for DepNode<'_> {
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

impl<'tcx> DepNode<'tcx> {
    /// Constructs a new [`DepNode`].
    ///
    /// The `tcx` and `body` arguments are used to precompute a pretty string
    /// representation of the [`DepNode`].
    pub fn new(
        place: Place<'tcx>,
        at: CallString,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        is_split: bool,
    ) -> Self {
        let i = at.leaf();
        let span = match i.location {
            RichLocation::Location(loc) => {
                let expanded_span = body
                    .stmt_at(loc)
                    .either(|s| s.source_info.span, |t| t.source_info.span);
                tcx.sess.source_map().stmt_span(expanded_span, body.span)
            }
            RichLocation::Start | RichLocation::End => tcx.def_span(i.function),
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

impl DepNode<'_> {
    /// Returns a pretty string representation of the place, if one exists.
    pub fn place_pretty(&self) -> Option<&str> {
        self.place_pretty.map(|s| s.as_ref().as_str())
    }
}

impl fmt::Display for DepNode<'_> {
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DepEdge {
    /// Either data or control.
    pub kind: DepEdgeKind,

    /// The location of the operation.
    pub at: CallString,

    pub source_use: SourceUse,

    pub target_use: TargetUse,
}

impl DepEdge {
    /// Constructs a data edge.
    pub fn data(at: CallString, source_use: SourceUse, target_use: TargetUse) -> Self {
        DepEdge {
            kind: DepEdgeKind::Data,
            at,
            source_use,
            target_use,
        }
    }

    /// Constructs a control edge.
    pub fn control(at: CallString, source_use: SourceUse, target_use: TargetUse) -> Self {
        DepEdge {
            kind: DepEdgeKind::Control,
            at,
            source_use,
            target_use,
        }
    }
}

impl fmt::Display for DepEdge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}\n@ {}", self.kind, self.at)
    }
}

/// The top-level PDG.
#[derive(Debug)]
pub struct DepGraph<'tcx> {
    /// The petgraph representation of the PDG.
    pub graph: DiGraph<DepNode<'tcx>, DepEdge>,
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
    pub fn new(graph: DiGraph<DepNode<'tcx>, DepEdge>) -> Self {
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
pub struct PartialGraph<'tcx> {
    pub(crate) nodes: FxHashSet<DepNode<'tcx>>,
    pub(crate) edges: FxHashSet<(DepNode<'tcx>, DepNode<'tcx>, DepEdge)>,
    pub(crate) generics: GenericArgsRef<'tcx>,
    def_id: DefId,
    arg_count: usize,
    local_decls: IndexVec<Local, LocalDecl<'tcx>>,
}

impl<'tcx> HasLocalDecls<'tcx> for PartialGraph<'tcx> {
    fn local_decls(&self) -> &LocalDecls<'tcx> {
        &self.local_decls
    }
}

impl<'tcx> PartialGraph<'tcx> {
    pub fn mentioned_call_string<'a>(
        &'a self,
    ) -> impl Iterator<Item = CallString> + Captures<'tcx> + 'a {
        self.nodes
            .iter()
            .map(|n| &n.at)
            .chain(self.edges.iter().map(|e| &e.2.at))
            .copied()
    }

    pub fn new(
        generics: GenericArgsRef<'tcx>,
        def_id: DefId,
        arg_count: usize,
        local_decls: &LocalDecls<'tcx>,
    ) -> Self {
        Self {
            nodes: Default::default(),
            edges: Default::default(),
            generics,
            def_id,
            arg_count,
            local_decls: local_decls.to_owned(),
        }
    }

    /// Returns the set of source places that the parent can access (write to)
    ///
    /// Parameterized by a `is_at_root` function which returns whether a given
    /// call string refers to a location in the outermost function. This is
    /// necessary, because consumers of [`PartialGraph`] manipulate the call
    /// string and as such we cannot assume that `.len() == 1` necessarily refers
    /// to a root location. (TODO we probably should maintain that invariant)
    pub(crate) fn parentable_srcs<'a>(
        &'a self,
        is_at_root: impl Fn(CallString) -> bool,
    ) -> FxHashSet<(DepNode<'tcx>, Option<u8>)> {
        self.edges
            .iter()
            .map(|(src, _, _)| *src)
            .filter(|n| is_at_root(n.at) && n.at.leaf().location.is_start())
            .filter_map(move |a| Some((a, as_arg(&a, self.def_id, self.arg_count)?)))
            .collect()
    }

    /// Returns the set of destination places that the parent can access (read
    /// from)
    ///
    /// Parameterized by a `is_at_root` function which returns whether a given
    /// call string refers to a location in the outermost function. This is
    /// necessary, because consumers of [`PartialGraph`] manipulate the call
    /// string and as such we cannot assume that `.len() == 1` necessarily refers
    /// to a root location. (TODO we probably should maintain that invariant)
    pub(crate) fn parentable_dsts<'a>(
        &'a self,
        is_at_root: impl Fn(CallString) -> bool,
    ) -> FxHashSet<(DepNode<'tcx>, Option<u8>)> {
        self.edges
            .iter()
            .map(|(_, dst, _)| *dst)
            .filter(|n| is_at_root(n.at) && n.at.leaf().location.is_end())
            .filter_map(move |a| Some((a, as_arg(&a, self.def_id, self.arg_count)?)))
            .collect()
    }
}

fn as_arg(node: &DepNode<'_>, def_id: DefId, arg_count: usize) -> Option<Option<u8>> {
    if node.at.leaf().function != def_id {
        return None;
    }
    let local = node.place.local.as_usize();
    if node.place.local == rustc_middle::mir::RETURN_PLACE {
        Some(None)
    } else if local > 0 && (local - 1) < arg_count {
        Some(Some(node.place.local.as_u32() as u8 - 1))
    } else {
        None
    }
}

impl<'tcx> TransformCallString for PartialGraph<'tcx> {
    fn transform_call_string(&self, f: impl Fn(CallString) -> CallString) -> Self {
        let recurse_node = |n: &DepNode<'tcx>| n.transform_call_string(&f);
        Self {
            generics: self.generics,
            nodes: self.nodes.iter().map(recurse_node).collect(),
            edges: self
                .edges
                .iter()
                .map(|(from, to, e)| {
                    (
                        recurse_node(from),
                        recurse_node(to),
                        e.transform_call_string(&f),
                    )
                })
                .collect(),
            def_id: self.def_id,
            arg_count: self.arg_count,
            local_decls: self.local_decls.to_owned(),
        }
    }
}

pub(crate) trait TransformCallString {
    fn transform_call_string(&self, f: impl Fn(CallString) -> CallString) -> Self;
}

impl TransformCallString for CallString {
    fn transform_call_string(&self, f: impl Fn(CallString) -> CallString) -> Self {
        f(*self)
    }
}

impl TransformCallString for DepNode<'_> {
    fn transform_call_string(&self, f: impl Fn(CallString) -> CallString) -> Self {
        Self {
            at: f(self.at),
            ..*self
        }
    }
}

impl TransformCallString for DepEdge {
    fn transform_call_string(&self, f: impl Fn(CallString) -> CallString) -> Self {
        Self {
            at: f(self.at),
            ..*self
        }
    }
}

pub(crate) fn push_call_string_root<T: TransformCallString>(
    old: &T,
    new_root: GlobalLocation,
) -> T {
    old.transform_call_string(|c| c.push_front(new_root))
}
