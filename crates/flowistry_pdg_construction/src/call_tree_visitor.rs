use flowistry_pdg::GlobalLocation;
use rustc_middle::{mir::Location, ty::Instance};

use crate::{
    graph::{DepEdge, DepNode, OneHopLocation, PartialGraph},
    MemoPdgConstructor,
};

pub struct CallTreeVisitor<'tcx, 'c> {
    memo: &'c MemoPdgConstructor<'tcx>,
    call_string_stack: Vec<GlobalLocation>,
    current_function: Instance<'tcx>,
}

impl<'tcx, 'c> CallTreeVisitor<'tcx, 'c> {
    pub fn new(memo: &'c MemoPdgConstructor<'tcx>, start: Instance<'tcx>) -> Self {
        Self {
            memo,
            call_string_stack: Vec::new(),
            current_function: start,
        }
    }

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
        self.current_function
    }
}

pub trait CallTreeVisit<'tcx> {
    fn visit_partial_graph(
        &mut self,
        vis: &mut CallTreeVisitor<'tcx, '_>,
        partial_graph: &PartialGraph<'tcx>,
    ) {
        vis.visit_partial_graph(self, partial_graph);
    }

    fn visit_edge(
        &mut self,
        vis: &mut CallTreeVisitor<'tcx, '_>,
        src: &DepNode<'tcx, OneHopLocation>,
        dst: &DepNode<'tcx, OneHopLocation>,
        kind: &DepEdge<OneHopLocation>,
    ) {
    }

    fn visit_node(
        &mut self,
        vis: &mut CallTreeVisitor<'tcx, '_>,
        node: &DepNode<'tcx, OneHopLocation>,
    ) {
    }

    fn visit_inlined_call(
        &mut self,
        vis: &mut CallTreeVisitor<'tcx, '_>,
        loc: Location,
        inst: Instance<'tcx>,
        ctrl_inputs: &[(DepNode<'tcx, OneHopLocation>, DepEdge<OneHopLocation>)],
    ) {
    }
}

impl<'tcx, 'c> CallTreeVisitor<'tcx, 'c> {
    pub fn visit_partial_graph<V: CallTreeVisit<'tcx> + ?Sized>(
        &mut self,
        vis: &mut V,
        graph: &PartialGraph<'tcx>,
    ) {
        for node in &graph.nodes {
            vis.visit_node(self, node);
        }
        for (src, dst, kind) in &graph.edges {
            vis.visit_edge(self, src, dst, kind);
        }
        for (loc, inst, ctrl_inputs) in &graph.inlined_calls {
            vis.visit_inlined_call(self, *loc, *inst, &ctrl_inputs);
        }
    }

    pub fn visit_inlined_call<V: CallTreeVisit<'tcx> + ?Sized>(
        &mut self,
        vis: &mut V,
        loc: Location,
        inst: Instance<'tcx>,
    ) {
        self.with_pushed_stack(
            GlobalLocation {
                function: self.current_function().def_id(),
                location: loc.into(),
            },
            |slf| {
                let old_fn = std::mem::replace(&mut slf.current_function, inst);
                let graph = slf.memo.construct_for(inst).unwrap();
                vis.visit_partial_graph(slf, &graph);
                slf.current_function = old_fn;
            },
        );
    }

    pub fn start<V: CallTreeVisit<'tcx> + ?Sized>(&mut self, vis: &mut V) {
        vis.visit_partial_graph(
            self,
            &self.memo.construct_for(self.current_function).unwrap(),
        );
    }
}
