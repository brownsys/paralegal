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
    graph::{DepEdge, DepNode, OneHopLocation, PartialGraph},
    MemoPdgConstructor,
};

pub struct VisitDriver<'tcx, 'c, K: Clone> {
    memo: &'c MemoPdgConstructor<'tcx, K>,
    call_string_stack: Vec<GlobalLocation>,
    current: (Instance<'tcx>, Rc<Cow<'c, PartialGraph<'tcx, K>>>),
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
        self.current.0
    }

    pub fn current_graph(&self) -> &PartialGraph<'tcx, K> {
        use std::borrow::Borrow;
        self.current.1.as_ref().borrow()
    }

    pub fn current_graph_as_rc(&self) -> Rc<Cow<'c, PartialGraph<'tcx, K>>> {
        self.current.1.clone()
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
        _src: &DepNode<'tcx, OneHopLocation>,
        _dst: &DepNode<'tcx, OneHopLocation>,
        _kind: &DepEdge<OneHopLocation>,
    ) {
    }

    fn visit_node(
        &mut self,
        _vis: &mut VisitDriver<'tcx, '_, K>,
        _node: &DepNode<'tcx, OneHopLocation>,
    ) {
    }

    fn visit_inlined_call(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_, K>,
        loc: Location,
        inst: Instance<'tcx>,
        k: &K,
        _ctrl_inputs: &[(DepNode<'tcx, OneHopLocation>, DepEdge<OneHopLocation>)],
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
            current: (start, Rc::new(g)),
            _k: k,
        }
    }
    pub fn visit_partial_graph<V: Visitor<'tcx, K> + ?Sized>(
        &mut self,
        vis: &mut V,
        graph: &PartialGraph<'tcx, K>,
    ) {
        for node in &graph.nodes {
            vis.visit_node(self, node);
        }
        for (src, dst, kind) in &graph.edges {
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
                let old = std::mem::replace(
                    &mut slf.current,
                    (
                        inst,
                        Rc::new(slf.memo.construct_for((inst, k.clone())).unwrap()),
                    ),
                );
                let graph: Rc<_> = slf.current.1.clone();
                vis.visit_partial_graph(slf, &graph);
                slf.current = old;
            },
        );
    }

    pub fn start<V: Visitor<'tcx, K> + ?Sized>(&mut self, vis: &mut V) {
        let g = self.current.1.clone();
        vis.visit_partial_graph(self, &g);
    }
}
