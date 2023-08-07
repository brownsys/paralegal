use crate::{
    ir::{regal, GlobalLocation},
    mir, serde,
    utils::{write_sep, DisplayViaDebug, TinyBitSet},
    DefId, Either,
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

#[derive(Clone, Eq, PartialEq, Hash, Copy, serde::Serialize, serde::Deserialize)]
pub struct Edge {
    data: TinyBitSet,
    control: bool,
}

impl Edge {
    #[inline]
    pub fn is_empty(self) -> bool {
        !self.control && self.data.is_empty()
    }
    #[inline]
    pub fn add_type(&mut self, t: EdgeType) {
        match t {
            EdgeType::Control => self.control = true,
            EdgeType::Data(i) => self.data.set(i),
        }
    }
    #[inline]
    pub fn empty() -> Self {
        Self {
            control: false,
            data: TinyBitSet::new_empty(),
        }
    }
    #[inline]
    pub fn merge(&mut self, other: Self) {
        self.control |= other.control;
        self.data |= other.data;
    }
    #[inline]
    pub fn into_types_iter(self) -> impl Iterator<Item = EdgeType> {
        self.data
            .into_iter_set_in_domain()
            .map(EdgeType::Data)
            .chain(self.control.then_some(EdgeType::Control))
    }
    #[inline]
    pub fn into_iter_data(self) -> impl Iterator<Item = u32> {
        self.data.into_iter_set_in_domain()
    }
    #[inline]
    pub fn count(self) -> u32 {
        self.data.count() + if self.control { 1 } else { 0 }
    }
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
    pub fn has_type(self, t: EdgeType) -> bool {
        match t {
            EdgeType::Control => self.control,
            EdgeType::Data(dat) => self.data.is_set(dat),
        }
    }
    #[inline]
    pub fn is_data(self) -> bool {
        !self.data.is_empty()
    }
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

impl<'g> GlobalLocal<'g> {
    pub fn at_root(local: mir::Local) -> Self {
        Self {
            local,
            location: None,
        }
    }

    pub fn relative(local: mir::Local, location: GlobalLocation<'g>) -> Self {
        Self {
            local,
            location: Some(location),
        }
    }
}

impl std::fmt::Display for GlobalLocal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} @ ", self.local)?;
        if let Some(loc) = self.location {
            write!(f, "{}", loc)
        } else {
            f.write_str("root")
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Debug, Hash)]
pub struct GlobalLocal<'g> {
    pub(super) local: mir::Local,
    location: Option<GlobalLocation<'g>>,
}

impl<'g> GlobalLocal<'g> {
    #[inline]
    pub fn local(self) -> mir::Local {
        self.local
    }

    #[inline]
    pub fn location(self) -> Option<GlobalLocation<'g>> {
        self.location
    }
}

/// Common, parameterized equation type used by the [`GraphResolver`]s
pub type Equation<L> = algebra::Equality<L, DisplayViaDebug<mir::Field>>;
pub type Equations<L> = Vec<Equation<L>>;
/// Common, parameterized graph type used in this module
pub type GraphImpl<L> = pg::GraphMap<Node<(L, DefId)>, Edge, pg::Directed>;

pub struct InlinedGraph<'g> {
    pub graph: GraphImpl<GlobalLocation<'g>>,
    pub equations: Equations<GlobalLocal<'g>>,
    pub num_inlined: usize,
    pub max_call_stack_depth: usize,
}

impl<'g> InlinedGraph<'g> {
    pub fn graph(&self) -> &GraphImpl<GlobalLocation<'g>> {
        &self.graph
    }

    pub fn vertex_count(&self) -> usize {
        self.graph.node_count()
    }

    pub fn edge_count(&self) -> usize {
        self.graph
            .all_edges()
            .map(|(_, _, w)| w.count() as usize)
            .sum()
    }

    pub fn inlined_functions_count(&self) -> usize {
        self.num_inlined
    }

    pub fn max_call_stack_depth(&self) -> usize {
        self.max_call_stack_depth
    }
}

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
