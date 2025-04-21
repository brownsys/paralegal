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
//!
//! There is a similar module in the `flowistry_pdg_construction` crate, This is
//! the non-rustc variant and used in policies.

use flowistry_pdg::{rustc_portable::Location, GlobalLocation};

use crate::{CallString, InlinedCallMeta, Instance, ProgramDescription, SPDG};

pub struct VisitDriver<'d> {
    program: &'d ProgramDescription,
    call_string_stack: CallString,
    current_function: Instance,
}

impl<'d> VisitDriver<'d> {
    pub fn new(program: &'d ProgramDescription, start: Instance) -> Self {
        Self {
            program,
            call_string_stack: CallString::empty(),
            current_function: start,
        }
    }

    pub fn with_pushed_stack<F, R>(&mut self, location: GlobalLocation, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        self.call_string_stack = self.call_string_stack.push(location);
        let result = f(self);
        self.call_string_stack = self.call_string_stack.pop().unwrap();
        result
    }

    pub fn call_stack(&self) -> CallString {
        self.call_string_stack
    }

    pub fn current_function(&self) -> Instance {
        self.current_function
    }
}

pub trait Visitor<'d> {
    fn visit_spdg(&mut self, vis: &mut VisitDriver<'d>, partial_graph: &SPDG) {
        vis.visit_spdg(self, partial_graph);
    }

    fn visit_inlined_call(
        &mut self,
        vis: &mut VisitDriver<'d>,
        loc: Location,
        meta: &InlinedCallMeta,
    ) {
        vis.visit_inlined_call(self, loc, meta);
    }
}

impl<'d> VisitDriver<'d> {
    pub fn visit_spdg<V: Visitor<'d> + ?Sized>(&mut self, vis: &mut V, graph: &SPDG) {
        for (loc, meta) in &graph.inlined_calls {
            vis.visit_inlined_call(self, *loc, meta);
        }
    }

    pub fn visit_inlined_call<V: Visitor<'d> + ?Sized>(
        &mut self,
        vis: &mut V,
        loc: Location,
        meta: &InlinedCallMeta,
    ) {
        self.with_pushed_stack(
            GlobalLocation {
                function: self.current_function().def_id,
                location: loc.into(),
            },
            |slf| {
                let old_fn = std::mem::replace(&mut slf.current_function, meta.instance);
                let graph = &slf.program.graphs[&meta.instance];
                vis.visit_spdg(slf, &graph);
                slf.current_function = old_fn;
            },
        );
    }

    pub fn start<V: Visitor<'d> + ?Sized>(&mut self, vis: &mut V) {
        vis.visit_spdg(self, &self.program.graphs[&self.current_function]);
    }
}
