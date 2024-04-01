use std::rc::Rc;

use either::Either;
use itertools::Itertools;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, Body, Location, Operand, Rvalue, Statement, StatementKind,
        Terminator, TerminatorKind,
    },
    ty::{GenericArgsRef, TyCtxt},
};

use crate::construct::{CallKind, PartialGraph};

use super::calling_convention::*;
use super::construct::GraphConstructor;
use super::utils::{self, FnResolution};

/// Stores ids that are needed to construct projections around async functions.
pub(crate) struct AsyncInfo {
    pub poll_ready_variant_idx: VariantIdx,
    pub poll_ready_field_idx: FieldIdx,
}

impl AsyncInfo {
    pub fn make(tcx: TyCtxt) -> Option<Rc<Self>> {
        let lang_items = tcx.lang_items();
        let poll_def = tcx.adt_def(lang_items.poll()?);
        let ready_vid = lang_items.poll_ready_variant()?;
        assert_eq!(poll_def.variant_with_id(ready_vid).fields.len(), 1);
        Some(Rc::new(Self {
            poll_ready_variant_idx: poll_def.variant_index_with_id(ready_vid),
            poll_ready_field_idx: 0_u32.into(),
        }))
    }
}

pub fn try_as_async_trait_function<'tcx>(
    tcx: TyCtxt,
    def_id: DefId,
    body: &Body<'tcx>,
) -> Option<(LocalDefId, GenericArgsRef<'tcx>, Location)> {
    if !has_async_trait_signature(tcx, def_id) {
        return None;
    }
    let mut matching_statements =
        body.basic_blocks
            .iter_enumerated()
            .flat_map(|(block, bbdat)| {
                bbdat.statements.iter().enumerate().filter_map(
                    move |(statement_index, statement)| {
                        let (def_id, generics) = match_async_trait_assign(statement)?;
                        Some((
                            def_id.as_local()?,
                            generics,
                            Location {
                                block,
                                statement_index,
                            },
                        ))
                    },
                )
            })
            .collect::<Vec<_>>();
    assert_eq!(matching_statements.len(), 1);
    matching_statements.pop()
}

pub fn match_async_trait_assign<'tcx>(
    statement: &Statement<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    match &statement.kind {
        StatementKind::Assign(box (
            _,
            Rvalue::Aggregate(box AggregateKind::Generator(def_id, generic_args, _), _args),
        )) => Some((*def_id, *generic_args)),
        _ => None,
    }
}

/// Does this function have a structure as created by the `#[async_trait]` macro
pub fn is_async_trait_fn(tcx: TyCtxt, def_id: DefId, body: &Body<'_>) -> bool {
    try_as_async_trait_function(tcx, def_id, body).is_some()
}

fn has_async_trait_signature(tcx: TyCtxt, def_id: DefId) -> bool {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        let sig = tcx.fn_sig(def_id).skip_binder();
        assoc_item.container == ty::AssocItemContainer::ImplContainer
            && assoc_item.trait_item_def_id.is_some()
            && match_pin_box_dyn_ty(tcx.lang_items(), sig.output().skip_binder())
    } else {
        false
    }
}

use rustc_middle::ty;
fn match_pin_box_dyn_ty(lang_items: &rustc_hir::LanguageItems, t: ty::Ty) -> bool {
    let ty::TyKind::Adt(pin_ty, args) = t.kind() else {
        return false;
    };
    if Some(pin_ty.did()) != lang_items.pin_type() {
        return false;
    };
    let [arg] = args.as_slice() else { return false };
    let Some(t_a) = arg.as_type() else {
        return false;
    };
    if !t_a.is_box() {
        return false;
    };
    let ty::TyKind::Dynamic(pred, _, ty::DynKind::Dyn) = t_a.boxed_ty().kind() else {
        return false;
    };
    if pred.len() != 2 {
        return false;
    }
    pred.iter().any(|p| {
        let ty::ExistentialPredicate::Trait(t) = p.skip_binder() else {
            return false;
        };
        Some(t.def_id) == lang_items.future_trait()
    })
}

fn get_async_generator<'tcx>(body: &Body<'tcx>) -> (LocalDefId, GenericArgsRef<'tcx>, Location) {
    let block = BasicBlock::from_usize(0);
    let location = Location {
        block,
        statement_index: body.basic_blocks[block].statements.len() - 1,
    };
    let stmt = body
        .stmt_at(location)
        .expect_left("Async fn should have a statement");
    let StatementKind::Assign(box (
        _,
        Rvalue::Aggregate(box AggregateKind::Generator(def_id, generic_args, _), _args),
    )) = &stmt.kind
    else {
        panic!("Async fn should assign to a generator")
    };
    (def_id.expect_local(), generic_args, location)
}

pub fn determine_async<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &Body<'tcx>,
) -> Option<(FnResolution<'tcx>, Location)> {
    let (generator_def_id, args, loc) = if tcx.asyncness(def_id).is_async() {
        get_async_generator(body)
    } else {
        try_as_async_trait_function(tcx, def_id.to_def_id(), body)?
    };
    let param_env = tcx.param_env(def_id);
    let generator_fn =
        utils::try_resolve_function(tcx, generator_def_id.to_def_id(), param_env, args);
    Some((generator_fn, loc))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AsyncDeterminationResult<T> {
    Resolved(T),
    Unresolvable(String),
    NotAsync,
}

impl<'tcx> GraphConstructor<'tcx> {
    pub(crate) fn try_handle_as_async(&self) -> Option<PartialGraph<'tcx>> {
        if self.calling_context.is_some() {
            return None;
        }
        let (generator_fn, location) = determine_async(self.tcx, self.def_id, &self.body)?;

        let calling_context = self.calling_context_for(generator_fn.def_id(), location);
        let params = self.pdg_params_for_call(generator_fn);
        Some(
            GraphConstructor::new(
                params,
                Some(calling_context),
                self.async_info.clone(),
                &self.pdg_cache,
            )
            .construct_partial(),
        )
    }

    pub(crate) fn try_poll_call_kind<'a>(
        &'a self,
        def_id: DefId,
        original_args: &'a [Operand<'tcx>],
    ) -> AsyncDeterminationResult<CallKind> {
        let lang_items = self.tcx.lang_items();
        if lang_items.future_poll_fn() == Some(def_id) {
            AsyncDeterminationResult::Resolved(CallKind::AsyncPoll)
        } else {
            AsyncDeterminationResult::NotAsync
        }
    }
}
