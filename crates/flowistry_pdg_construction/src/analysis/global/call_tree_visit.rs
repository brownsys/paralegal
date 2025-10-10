//! Machinery for visiting a monomorphized tree with access to intermediate PDGs.
//!
//! Each traversal is comprised of two components:
//! 1. A `VisitDriver` that drives the traversal and manages associated
//!    state. Mainly the currently visited function and the call stack.
//! 2. An object implementing `Visitor` which contains the custom logic of
//!    the traversal.
//!
//! The relation of the to is such that for each visitation step the `*_visit`
//! method on Visitor is called first. It should then call the corresponding
//! `*_visit` method on the VisitDriver which will take care of the recursion.

use std::{borrow::Cow, hash::Hash, rc::Rc};

use flowistry_pdg::{CallString, GlobalLocation, RichLocation};
use rustc_middle::{mir::Location, ty::Instance};

use crate::{analysis::global::partial_graph::NodeKey, DepNodeKind, MemoPdgConstructor};

use super::{
    graph_elems::{DepEdge, DepNode, OneHopLocation, PartialGraph},
    partial_graph::{GraphConnectionPoint, Node},
};

pub struct VisitDriver<'tcx, 'c, K: Clone> {
    memo: &'c MemoPdgConstructor<'tcx, K>,
    call_string_stack: Vec<GlobalLocation>,
    graph_stack: Vec<(Instance<'tcx>, Rc<Cow<'c, PartialGraph<'tcx, K>>>)>,
    _k: K,
    ctrl_inputs: Option<(usize, Box<[GraphConnectionPoint<'tcx, CallString>]>)>,
}

impl<'tcx, 'c, K: Clone> VisitDriver<'tcx, 'c, K> {
    pub fn with_pushed_stack<F, R>(&mut self, location: GlobalLocation, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        with_pushed_stack(self, |s| &mut s.call_string_stack, location, f)
    }

    pub fn call_stack(&self) -> &[GlobalLocation] {
        &self.call_string_stack
    }

    pub fn current_function(&self) -> Instance<'tcx> {
        self.graph_stack.last().unwrap().0
    }

    pub fn current_graph(&self) -> &PartialGraph<'tcx, K> {
        use std::borrow::Borrow;
        self.graph_stack.last().unwrap().1.as_ref().borrow()
    }

    pub fn current_graph_as_rc(&self) -> Rc<Cow<'c, PartialGraph<'tcx, K>>> {
        self.graph_stack.last().unwrap().1.clone()
    }

    pub fn globalize_location(&mut self, location: &OneHopLocation) -> CallString {
        self.with_pushed_stack(
            GlobalLocation {
                function: self.current_function().def_id(),
                location: location.location,
            },
            |vis| {
                if let Some((c, start)) = location.in_child {
                    vis.with_pushed_stack(
                        GlobalLocation {
                            function: c,
                            location: if start {
                                RichLocation::Start
                            } else {
                                RichLocation::End
                            },
                        },
                        |vis| CallString::new(vis.call_stack()),
                    )
                } else {
                    CallString::new(vis.call_stack())
                }
            },
        )
    }
}

pub trait Visitor<'tcx, K: Hash + Eq + Clone> {
    fn visit_partial_graph(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_, K>,
        partial_graph: &PartialGraph<'tcx, K>,
    ) {
        vis.visit_partial_graph(self, partial_graph);
    }

    fn visit_edge(
        &mut self,
        _vis: &mut VisitDriver<'tcx, '_, K>,
        _src: Node,
        _dst: Node,
        _kind: &DepEdge<OneHopLocation>,
    ) {
    }

    /// These nodes between the current graph and the caller should be
    /// considered the same.
    fn visit_parent_connection(
        &mut self,
        _vis: &mut VisitDriver<'tcx, '_, K>,
        _in_caller: Node,
        _in_this: Node,
        _is_at_start: bool,
    ) {
    }

    /// Visit a control edge coming from one of the callers of this function.
    /// This function is only called for destination nodes that do not already
    /// have incoming control flow edges.
    ///
    /// Note that _src is located in a caller graph, identified by the index.
    ///
    /// The index is which level in the call stack this control edge comes from,
    /// since they can sometimes skip a function.
    fn visit_ctrl_edge(
        &mut self,
        _vis: &mut VisitDriver<'tcx, '_, K>,
        _index: usize,
        _src: Node,
        _dst: Node,
        _kind: &DepEdge<CallString>,
    ) {
    }

    fn visit_node(
        &mut self,
        _vis: &mut VisitDriver<'tcx, '_, K>,
        _k: Node,
        _node: &DepNode<'tcx, OneHopLocation>,
    ) {
    }

    fn visit_inlined_call(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_, K>,
        loc: Location,
        inst: Instance<'tcx>,
        k: &K,
        ctrl_inputs: Box<[GraphConnectionPoint<'tcx, CallString>]>,
    ) {
        vis.visit_inlined_call(self, loc, inst, k, ctrl_inputs);
    }
}

impl<'tcx, 'c, K: Clone + Hash + Eq> VisitDriver<'tcx, 'c, K> {
    pub fn new(memo: &'c MemoPdgConstructor<'tcx, K>, start: Instance<'tcx>, k: K) -> Self
    where
        K: Clone,
    {
        let g = memo.construct_for((start, k.clone())).unwrap();
        Self {
            memo,
            call_string_stack: Vec::new(),
            graph_stack: vec![(start, Rc::new(g))],
            _k: k,
            ctrl_inputs: None,
        }
    }

    pub fn visit_partial_graph<V: Visitor<'tcx, K> + ?Sized>(
        &mut self,
        vis: &mut V,
        graph: &PartialGraph<'tcx, K>,
    ) {
        if self.graph_stack.len() > 1 {
            let parent = self.graph_stack[self.graph_stack.len() - 2].1.clone();
            let cloc = self.call_stack().last().unwrap().location;
            for (node, info) in parent.iter_nodes() {
                let DepNodeKind::Place(pkind) = &info.kind else {
                    continue;
                };
                if info.at.in_child.is_some_and(|(d, _)| d == graph.def_id)
                    && info.at.location == cloc
                {
                    let is_at_start = info.at.in_child.unwrap().1;
                    vis.visit_parent_connection(
                        self,
                        node,
                        graph
                            .get_node(&NodeKey::for_place(
                                pkind.place,
                                if is_at_start {
                                    RichLocation::Start
                                } else {
                                    RichLocation::End
                                }
                                .into(),
                            ))
                            .unwrap(),
                        is_at_start,
                    );
                }
            }
        }
        for (node, info) in graph.iter_nodes() {
            vis.visit_node(self, node, info);
        }
        for (src, dst, kind) in graph.iter_edges() {
            vis.visit_edge(self, src, dst, kind);
        }

        // Handle incoming control edges.
        if let Some((idx, ctrl_in)) = self.ctrl_inputs.take() {
            for (node, _) in graph.iter_nodes() {
                if !graph
                    .raw()
                    .edges_directed(node, petgraph::Direction::Incoming)
                    .any(|e| e.weight().is_control())
                {
                    for (src, edge) in ctrl_in.iter() {
                        vis.visit_ctrl_edge(self, idx, *src, node, edge);
                    }
                }
            }
            self.ctrl_inputs = Some((idx, ctrl_in));
        }

        for (loc, inst, k, ctrl_inputs) in &graph.inlined_calls {
            let globalized_ctrl_input = ctrl_inputs
                .iter()
                .map(|(src, edge)| (*src, edge.map_at(|a| self.globalize_location(a))))
                .collect();
            vis.visit_inlined_call(self, *loc, *inst, k, globalized_ctrl_input);
        }
    }

    pub fn visit_inlined_call<V: Visitor<'tcx, K> + ?Sized>(
        &mut self,
        vis: &mut V,
        loc: Location,
        inst: Instance<'tcx>,
        k: &K,
        ctrl_inputs: Box<[GraphConnectionPoint<'tcx, CallString>]>,
    ) {
        let swap_ctrl_input = !ctrl_inputs.is_empty();
        let old_ctrl_inputs = if swap_ctrl_input {
            std::mem::replace(
                &mut self.ctrl_inputs,
                Some((self.graph_stack.len() - 1, ctrl_inputs)),
            )
        } else {
            None
        };
        self.with_pushed_stack(
            GlobalLocation {
                function: self.current_function().def_id(),
                location: loc.into(),
            },
            |slf| {
                with_pushed_stack(
                    slf,
                    |s| &mut s.graph_stack,
                    (
                        inst,
                        Rc::new(slf.memo.construct_for((inst, k.clone())).unwrap()),
                    ),
                    |slf| {
                        let graph: Rc<_> = slf.current_graph_as_rc();
                        vis.visit_partial_graph(slf, &graph);
                    },
                )
            },
        );
        if swap_ctrl_input {
            self.ctrl_inputs = old_ctrl_inputs;
        }
    }

    pub fn start<V: Visitor<'tcx, K> + ?Sized>(&mut self, vis: &mut V) {
        let g = self.current_graph_as_rc();
        vis.visit_partial_graph(self, &g);
    }
}

fn with_pushed_stack<T, E, R>(
    obj: &mut T,
    access: impl Fn(&mut T) -> &mut Vec<E>,
    elem: E,
    inner: impl FnOnce(&mut T) -> R,
) -> R {
    let stack = access(obj);
    stack.push(elem);
    let len_before = stack.len();
    let result = inner(obj);
    let stack = access(obj);
    assert_eq!(stack.len(), len_before);
    stack.pop();
    result
}
