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

macro_rules! let_assert {
  ($p:pat = $e:expr, $($arg:tt)*) => {
    let $p = $e else {
      panic!($($arg)*);
    };
  }
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
                        let StatementKind::Assign(box (
                            _,
                            Rvalue::Aggregate(
                                box AggregateKind::Generator(def_id, generic_args, _),
                                _args,
                            ),
                        )) = &statement.kind
                        else {
                            return None;
                        };
                        Some((
                            def_id.as_local()?,
                            *generic_args,
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

impl<'tcx> GraphConstructor<'tcx> {
    pub(crate) fn try_handle_as_async(&self) -> Option<PartialGraph<'tcx>> {
        let (generator_def_id, generic_args, location) = self.determine_async()?;
        let param_env = self.tcx.param_env(self.def_id);
        let generator_fn = utils::try_resolve_function(
            self.tcx,
            generator_def_id.to_def_id(),
            param_env,
            generic_args,
        );
        let calling_context = self.calling_context_for(generator_def_id.to_def_id(), location);
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

    fn determine_async(&self) -> Option<(LocalDefId, GenericArgsRef<'tcx>, Location)> {
        if self.tcx.asyncness(self.def_id).is_async() {
            Some(Self::async_generator(&self.body))
        } else {
            try_as_async_trait_function(self.tcx, self.def_id.to_def_id(), self.body.as_ref())
        }
    }

    fn async_generator(body: &Body<'tcx>) -> (LocalDefId, GenericArgsRef<'tcx>, Location) {
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

    pub(crate) fn try_poll_call_kind<'a>(
        &'a self,
        def_id: DefId,
        original_args: &'a [Operand<'tcx>],
    ) -> Option<CallKind<'tcx, 'a>> {
        let lang_items = self.tcx.lang_items();
        if lang_items.future_poll_fn() == Some(def_id) {
            let (fun, loc, args) = self.find_async_args(original_args);
            Some(CallKind::AsyncPoll(fun, loc, args))
        } else {
            None
        }
    }
    /// Given the arguments to a `Future::poll` call, walk back through the
    /// body to find the original future being polled, and get the arguments to the future.
    fn find_async_args<'a>(
        &'a self,
        args: &'a [Operand<'tcx>],
    ) -> (
        FnResolution<'tcx>,
        Location,
        AsyncCallingConvention<'tcx, 'a>,
    ) {
        let get_def_for_op = |op: &Operand<'tcx>| -> Location {
            let_assert!(Some(place) = op.place(), "Arg is not a place");
            let_assert!(Some(local) = place.as_local(), "Place is not a local");
            let_assert!(
                Some(locs) = &self.body_assignments.get(&local),
                "Local has no assignments"
            );
            assert!(locs.len() == 1);
            locs[0]
        };

        let_assert!(
            Either::Right(Terminator {
                kind: TerminatorKind::Call {
                    args: new_pin_args,
                    ..
                },
                ..
            }) = &self.body.stmt_at(get_def_for_op(&args[0])),
            "Pinned assignment is not a call"
        );
        debug_assert!(new_pin_args.len() == 1);

        let future_aliases = self
            .aliases(self.tcx.mk_place_deref(new_pin_args[0].place().unwrap()))
            .collect_vec();
        debug_assert!(future_aliases.len() == 1);
        let future = *future_aliases.first().unwrap();

        let_assert!(
          Either::Left(Statement {
            kind: StatementKind::Assign(box (_, Rvalue::Use(future2))),
            ..
          }) = &self.body.stmt_at(get_def_for_op(&Operand::Move(future))),
          "Assignment to pin::new input is not a statement"
        );

        let_assert!(
            Either::Right(Terminator {
                kind: TerminatorKind::Call {
                    args: into_future_args,
                    ..
                },
                ..
            }) = &self.body.stmt_at(get_def_for_op(future2)),
            "Assignment to alias of pin::new input is not a call"
        );

        let mut chase_target = Err(&into_future_args[0]);

        while let Err(target) = chase_target {
            let async_fn_call_loc = get_def_for_op(target);
            let stmt = &self.body.stmt_at(async_fn_call_loc);
            chase_target = match stmt {
                Either::Right(Terminator {
                    kind: TerminatorKind::Call { args, func, .. },
                    ..
                }) => {
                    let (op, generics) = self.operand_to_def_id(func).unwrap();
                    Ok((
                        op,
                        generics,
                        AsyncCallingConvention::Fn(args),
                        async_fn_call_loc,
                    ))
                }
                Either::Left(Statement { kind, .. }) => match kind {
                    StatementKind::Assign(box (
                        _,
                        Rvalue::Aggregate(
                            box AggregateKind::Generator(def_id, generic_args, _),
                            args,
                        ),
                    )) => Ok((
                        *def_id,
                        *generic_args,
                        AsyncCallingConvention::Block(args),
                        async_fn_call_loc,
                    )),
                    StatementKind::Assign(box (_, Rvalue::Use(target))) => Err(target),
                    _ => {
                        panic!("Assignment to into_future input is not a call: {stmt:?}");
                    }
                },
                _ => {
                    panic!("Assignment to into_future input is not a call: {stmt:?}");
                }
            };
        }

        let (op, generics, calling_convention, async_fn_call_loc) = chase_target.unwrap();

        let resolution =
            utils::try_resolve_function(self.tcx, op, self.tcx.param_env(self.def_id), generics);

        (resolution, async_fn_call_loc, calling_convention)
    }
}
