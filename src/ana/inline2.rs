use crate::{
    ir::GLI,
    ir::{regal, GlobalLocation, global_location::GliAt},
    rust::hir::{def_id::DefId, BodyId},
    utils::DisplayViaDebug,
    HashMap, TyCtxt, mir, Either
};

use std::{cell::RefCell, rc::Rc};

use super::inline::InlineSelector;

pub struct Inliner<'tcx, 'g, 's> {
    base_memo: regal::MemoizingConstructor<'tcx, 'g>,
    inline_memo: RefCell<HashMap<BodyId, Rc<regal::Body<GlobalLocation<'g>>>>>,
    recurse_selector: &'s dyn InlineSelector,
}

impl<'tcx, 'g, 's> Inliner<'tcx, 'g, 's> {
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.base_memo.tcx()
    }

    pub fn gli(&self) -> GLI<'g> {
        self.base_memo.gli()
    }

    pub fn new(tcx: TyCtxt<'tcx>, gli: GLI<'g>, recurse_selector: &'s dyn InlineSelector)-> Self {
        let base_memo = regal::MemoizingConstructor::new(tcx, gli);
        Self {
            base_memo,
            recurse_selector,
            inline_memo: Default::default(),
        }
    }

    fn expand_dependency(&self, dependency: &regal::Dependency<DisplayViaDebug<mir::Location>>, local: &regal::Body<DisplayViaDebug<mir::Location>>, body_id: BodyId) -> impl Iterator<Item=regal::Dependency<GlobalLocation<'g>>> {
        let only_self = || Box::new(std::iter::once(dependency.map_locations(|l| self.gli().globalize_location(**l, body_id)))) as Box<dyn Iterator<Item=regal::Dependency<GlobalLocation<'g>>>>;
        if let regal::Target::Call(l) = dependency.target {
            let target_call = local.calls[&l];
            match target_call.function.as_local() {
                Some(local_def_id) if self.recurse_selector.should_inline(self.tcx(), local_def_id) => {
                    let hir = self.tcx().hir();
                    self.get(hir.body_owned_by(hir.local_def_id_to_hir_id(local_def_id)))
                        .return_state
                }
                _ => only_self(),
            }
        } else {
            only_self()
        }
    }

    fn handle_call(&self, loc: mir::Location, call: &regal::Call<DisplayViaDebug<mir::Location>>, body_id: BodyId, local: &regal::Body<DisplayViaDebug<mir::Location>>) -> impl Iterator<Item=(GlobalLocation<'g>, regal::Call<GlobalLocation<'g>>)> {
        let gli_at = self.gli().at(loc, body_id);
        match call.function.as_local() {
            Some(local_def_id) if self.recurse_selector.should_inline(self.tcx(), local_def_id) => {
                Either::Left({
                    let hir = self.tcx().hir();
                    self.get(hir.body_owned_by(hir.local_def_id_to_hir_id(local_def_id)))
                        .calls()
                        .iter()
                        .map(move |(key, inner_callsite)| 
                            (gli_at.relativize(*key), inner_callsite.map_locations(|l| gli_at.relativize(*l)).expand_arguments(|arg, term| {
                                let term = term.clone();
                                call.arguments[arg].iter().filter_map(move |dep| {
                                    let mut new_term = term.clone();
                                    new_term.sub(dep.target_term.clone());
                                    new_term.simplify().then(|| {
                                        regal::Dependency {
                                            target_term: new_term,
                                            target: dep.target
                                        }
                                    })
                                })
                                .flat_map(|dep| self.expand_dependency(&dep))
                            })))
                        .collect::<Vec<_>>()
                        .into_iter()
                })
            }
            _ => Either::Right(std::iter::once((gli_at.as_global_location(), call.flat_map_dependencies(|f| self.expand_dependency(f)))))
        }.into_iter()
    }

    pub fn get(&self, body_id: BodyId) -> Rc<regal::Body<GlobalLocation<'g>>> {
        if let Some(b) = self.inline_memo.borrow().get(&body_id) {
            return b.clone();
        }

        let local = self.base_memo.get(body_id);

        let calls = local.calls().iter().flat_map(|(loc, call)| {
            self.handle_call(**loc, call, body_id, local)
        }).collect();

        let return_state = 
            local.return_state.iter().flat_map(|dep| self.expand_dependency(dep)).collect();

        let body = Rc::new(regal::Body {
            calls, return_state
        });

        self.inline_memo.borrow_mut().insert(body_id, body.clone());
        body
    }
}
