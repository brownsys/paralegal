use crate::{
    ir::{regal, GlobalLocation},
    mir, serde,
    utils::{time, write_sep, DisplayViaDebug, FnResolution, IntoDefId, TinyBitSet},
    BodyId, Either, HashMap, HashSet, Location, TyCtxt,
};

use super::algebra;

use petgraph::prelude as pg;

pub type ArgNum = u32;

pub type Node<C> = regal::SimpleLocation<C>;

impl<C> Node<C> {
    pub fn map_call<C0, F: FnOnce(&C) -> C0>(&self, f: F) -> Node<C0> {
        match self {
            Node::Return => Node::Return,
            Node::Argument(a) => Node::Argument(*a),
            Node::Call(c) => Node::Call(f(c)),
        }
    }
}

/// Efficently tracks what flows along the edge between two graph nodes.
///
/// The upstream node can influence the downstream node via control or via
/// dataflow into one of its arguments. Use [`Self::into_type_iter`] to see all
/// connections stored in this edge, or [`Self::has_type`] to query a specific
/// type of connection.
///
/// Construct an edge either with [`Self::empty`] and [`Self::add_type`] or use
/// the [`FromIterator`] instance, e.g. calling `collect` on an iterator of
/// [`EdgeType`].
///
/// This struct is tiny (smaller than a pointer), which is why it is [`Copy`]
/// and most methods take `self`.
///
/// Be aware that data edges are only supported in the range `0..15` and setting
/// or querying data edges outside of the range will cause panics.
#[derive(Clone, Eq, PartialEq, Hash, Copy, serde::Serialize, serde::Deserialize)]
pub struct Edge {
    data: TinyBitSet,
    control: bool,
}

impl Edge {
    /// Are there no connections on this edge?
    ///
    /// Empty edges whould be avoided. They should only occur as a result of
    /// prunging with [`Self::remove_type`] and an `is_empty` edge should then
    /// be deleted from the graph.
    #[inline]
    pub fn is_empty(self) -> bool {
        !self.control && self.data.is_empty()
    }
    /// Register an additional type in this edge.
    ///
    /// No errors are raised if the type already exists.
    #[inline]
    pub fn add_type(&mut self, t: EdgeType) {
        match t {
            EdgeType::Control => self.control = true,
            EdgeType::Data(i) => self.data.set(i),
        }
    }
    /// Construct a new empty edge.
    #[inline]
    pub fn empty() -> Self {
        Self {
            control: false,
            data: TinyBitSet::new_empty(),
        }
    }
    /// Combine two edges
    ///
    /// No errors are raised if the two overlap.
    #[inline]
    pub fn merge(&mut self, other: Self) {
        self.control |= other.control;
        self.data |= other.data;
    }
    /// Iterate all edge typers stored.
    #[inline]
    pub fn into_types_iter(self) -> impl Iterator<Item = EdgeType> {
        self.data
            .into_iter_set_in_domain()
            .map(EdgeType::Data)
            .chain(self.control.then_some(EdgeType::Control))
    }
    /// Iterate only the data edges.
    #[inline]
    pub fn into_iter_data(self) -> impl Iterator<Item = u32> {
        self.data.into_iter_set_in_domain()
    }
    /// How many types of connections are combined in this edge?
    ///
    /// More efficient version of `self.into_types_iter().count()`
    #[inline]
    pub fn count(self) -> u32 {
        self.data.count() + if self.control { 1 } else { 0 }
    }
    /// Delete this type from the edge.
    ///
    /// No error is raised if this type was not present.
    #[inline]
    pub fn remove_type(&mut self, t: EdgeType) -> bool {
        let changed;
        match t {
            EdgeType::Control => {
                changed = self.control;
                self.control = false;
            }
            EdgeType::Data(i) => {
                changed = self.data.is_set(i);
                self.data.clear(i);
            }
        }
        changed
    }
    /// Query if this connection type is present in the edge.
    pub fn has_type(self, t: EdgeType) -> bool {
        match t {
            EdgeType::Control => self.control,
            EdgeType::Data(dat) => self.data.is_set(dat),
        }
    }
    /// Are there any data connections?
    #[inline]
    pub fn is_data(self) -> bool {
        !self.data.is_empty()
    }
    /// Is there a control flow connection?
    #[inline]
    pub fn is_control(self) -> bool {
        self.control
    }
}

impl FromIterator<EdgeType> for Edge {
    fn from_iter<T: IntoIterator<Item = EdgeType>>(iter: T) -> Self {
        let mut slf = Self::empty();
        for i in iter {
            slf.add_type(i)
        }
        slf
    }
}

/// Describes the type of connections that can be stored in an [`Edge`].
///
/// This is a supporting enum for [`Edge`] and used for most interactions with it.
///
/// Be aware that the `Data` variant is only supported in the range of `0..15`.
#[derive(Hash, Eq, PartialEq, Clone, Copy)]
pub enum EdgeType {
    Data(u32),
    Control,
}

impl std::fmt::Display for Edge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write_sep(
            f,
            ", ",
            self.data
                .into_iter_set_in_domain()
                .map(Either::Left)
                .chain(self.control.then_some(Either::Right(()))),
            |elem, f| match elem {
                Either::Left(i) => write!(f, "arg{i}"),
                Either::Right(()) => write!(f, "ctrl"),
            },
        )
    }
}

/// A [`mir::Local`] but also tracks the precise call chain it is reachable
/// from.
#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Debug, Hash)]
pub struct GlobalLocal {
    pub(super) local: mir::Local,
    location: Option<GlobalLocation>,
}

impl GlobalLocal {
    /// Construct a new global local in a root function (no call chain)
    pub fn at_root(local: mir::Local) -> Self {
        Self {
            local,
            location: None,
        }
    }

    /// Construct a new global local relative to this call chain.
    pub fn relative(local: mir::Local, location: GlobalLocation) -> Self {
        Self {
            local,
            location: Some(location),
        }
    }

    /// Access to the variable name.
    #[inline]
    pub fn local(self) -> mir::Local {
        self.local
    }

    /// Access to the call chain.
    #[inline]
    pub fn location(self) -> Option<GlobalLocation> {
        self.location
    }
}

impl std::fmt::Display for GlobalLocal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} @ ", self.local)?;
        if let Some(loc) = self.location {
            write!(f, "{}", loc)
        } else {
            f.write_str("root")
        }
    }
}

/// Common structure of equations used for inlining.
pub type Equation<L> = algebra::Equality<L, DisplayViaDebug<mir::Field>>;
/// Common structure of a collection of equations used for inlining.
pub type Equations<L> = Vec<Equation<L>>;
/// Common, parameterized graph type used in this module
pub type GraphImpl<'tcx, L> = pg::GraphMap<Node<(L, FnResolution<'tcx>)>, Edge, pg::Directed>;

/// A graph that has its subgraphs inlined (or is in the process of it).
pub struct InlinedGraph<'tcx> {
    /// The global graph
    pub(super) graph: GraphImpl<'tcx, GlobalLocation>,
    /// The global equations
    pub equations: Equations<GlobalLocal>,
    /// For statistics, how many functions did we inline
    pub(super) num_inlined: usize,
    /// For statistics: how deep a calll stack did we inline.
    pub(super) max_call_stack_depth: usize,
}

impl<'tcx> InlinedGraph<'tcx> {
    /// Access the actual graph.
    pub fn graph(&self) -> &GraphImpl<'tcx, GlobalLocation> {
        &self.graph
    }

    /// Access the number of nodes.
    pub fn vertex_count(&self) -> usize {
        self.graph.node_count()
    }

    /// Access the number of edges.
    pub fn edge_count(&self) -> usize {
        self.graph
            .all_edges()
            .map(|(_, _, w)| w.count() as usize)
            .sum()
    }

    /// How many functions did we inline?
    pub fn inlined_functions_count(&self) -> usize {
        self.num_inlined
    }

    /// What is the maximum depth of call stack we inlined
    pub fn max_call_stack_depth(&self) -> usize {
        self.max_call_stack_depth
    }

    /// Construct the initial graph from a [`regal::Body`]
    pub fn from_body(
        body_id: BodyId,
        body: &regal::Body<'tcx, DisplayViaDebug<Location>>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        time("Graph Construction From Regal Body", || {
            let equations = to_global_equations(&body.equations, body_id);
            let mut gwr = InlinedGraph {
                equations,
                graph: Default::default(),
                num_inlined: 0,
                max_call_stack_depth: 0,
            };
            let g = &mut gwr.graph;
            let call_map = body
                .calls
                .iter()
                .map(|(loc, call)| (loc, call.function))
                .collect::<HashMap<_, _>>();
            let return_node = g.add_node(Node::Return);

            let mut add_dep_edges =
                |to, idx, deps: &HashSet<regal::Target<DisplayViaDebug<Location>>>| {
                    for d in deps {
                        use regal::Target;
                        let from = match d {
                            Target::Call(c) => regal::SimpleLocation::Call((
                                GlobalLocation::single(**c, body_id),
                                *call_map.get(c).unwrap_or_else(|| {
                                    panic!(
                                        "Expected to find call at {c} in function {}",
                                        tcx.def_path_debug_str(body_id.into_def_id(tcx))
                                    )
                                }),
                            )),
                            Target::Argument(a) => regal::SimpleLocation::Argument(*a),
                        };
                        if g.contains_edge(from, to) {
                            g[(from, to)].add_type(idx)
                        } else {
                            let mut edge = Edge::empty();
                            edge.add_type(idx);
                            g.add_edge(from, to, edge);
                        }
                    }
                };

            for (&loc, call) in body.calls.iter() {
                let n = Node::Call((GlobalLocation::single(*loc, body_id), call.function));
                for (idx, deps) in call.arguments.iter().enumerate() {
                    if let Some((_, deps)) = deps {
                        add_dep_edges(n, EdgeType::Data(idx as u32), deps)
                    }
                }
                add_dep_edges(n, EdgeType::Control, &call.ctrl_deps);
            }
            add_dep_edges(return_node, EdgeType::Data(0_u32), &body.return_deps);
            for (idx, deps) in body.return_arg_deps.iter().enumerate() {
                add_dep_edges(Node::Argument(idx.into()), EdgeType::Data(0_u32), deps);
            }

            gwr
        })
    }
}

/// Globalize all locations mentioned in these equations.
fn to_global_equations(
    eqs: &Equations<DisplayViaDebug<mir::Local>>,
    _body_id: BodyId,
) -> Equations<GlobalLocal> {
    eqs.iter()
        .map(|eq| eq.map_bases(|target| GlobalLocal::at_root(**target)))
        .collect()
}

/// Add or merge the `weight` to the edge from `source` to `target` (directed).
pub fn add_weighted_edge<N: petgraph::graphmap::NodeTrait, D: petgraph::EdgeType>(
    g: &mut pg::GraphMap<N, Edge, D>,
    source: N,
    target: N,
    weight: Edge,
) {
    if let Some(prior_weight) = g.edge_weight_mut(source, target) {
        prior_weight.merge(weight)
    } else {
        g.add_edge(source, target, weight);
    }
}
