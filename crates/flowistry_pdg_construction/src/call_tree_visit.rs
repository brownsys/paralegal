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

use crate::{
    graph::{DepEdge, DepNode, GraphConnectionPoint, Node, OneHopLocation, PartialGraph},
    MemoPdgConstructor,
};

pub struct VisitDriver<'tcx, 'c, K: Clone> {
    memo: &'c MemoPdgConstructor<'tcx, K>,
    call_string_stack: Vec<GlobalLocation>,
    graph_stack: Vec<(Instance<'tcx>, Rc<Cow<'c, PartialGraph<'tcx, K>>>)>,
    _k: K,
}

impl<'tcx, 'c, K: Clone> VisitDriver<'tcx, 'c, K> {
    pub fn with_pushed_stack<F, R>(&mut self, location: GlobalLocation, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        self.call_string_stack.push(location);
        let result = f(self);
        self.call_string_stack.pop();
        result
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
        _ctrl_inputs: &[GraphConnectionPoint<'tcx>],
    ) {
        vis.visit_inlined_call(self, loc, inst, k);
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
                if info.at.in_child.is_some_and(|(d, _)| d == graph.def_id)
                    && info.at.location == cloc
                {
                    let is_at_start = info.at.in_child.unwrap().1;
                    vis.visit_parent_connection(
                        self,
                        node,
                        graph
                            .get_node(
                                info.place,
                                if is_at_start {
                                    RichLocation::Start
                                } else {
                                    RichLocation::End
                                }
                                .into(),
                            )
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
        for (loc, inst, k, ctrl_inputs) in &graph.inlined_calls {
            vis.visit_inlined_call(self, *loc, *inst, k, ctrl_inputs);
        }
    }

    pub fn visit_inlined_call<V: Visitor<'tcx, K> + ?Sized>(
        &mut self,
        vis: &mut V,
        loc: Location,
        inst: Instance<'tcx>,
        k: &K,
    ) {
        self.with_pushed_stack(
            GlobalLocation {
                function: self.current_function().def_id(),
                location: loc.into(),
            },
            |slf| {
                slf.graph_stack.push((
                    inst,
                    Rc::new(slf.memo.construct_for((inst, k.clone())).unwrap()),
                ));
                let graph: Rc<_> = slf.current_graph_as_rc();
                vis.visit_partial_graph(slf, &graph);
                slf.graph_stack.pop();
            },
        );
    }

    pub fn start<V: Visitor<'tcx, K> + ?Sized>(&mut self, vis: &mut V) {
        let g = self.current_graph_as_rc();
        vis.visit_partial_graph(self, &g);
    }
}
