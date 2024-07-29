use std::rc::Rc;

use either::Either;
use itertools::Itertools;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, Body, Location, Operand, Place, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{GenericArgsRef, Instance, TyCtxt},
};

use super::{
    local_analysis::{CallKind, LocalAnalysis},
    utils,
};

/// Describe in which way a function is `async`.
///
/// Critically distinguishes between a normal `async fn` and an
/// `#[async_trait]`.
#[derive(Debug, Clone, Copy)]
pub enum AsyncType {
    Fn,
    Trait,
}

/// Context for a call to [`Future::poll`](std::future::Future::poll), when
/// called on a future created via an `async fn` or an async block.
pub struct AsyncFnPollEnv<'tcx> {
    /// If the generator came from an `async fn`, then this is that function. If
    /// it is from an async block, this is `None`.
    pub async_fn_parent: Option<Instance<'tcx>>,
    /// Where was the `async fn` called, or where was the async block created.
    pub creation_loc: Location,
    /// A place which carries the runtime value representing the generator in
    /// the caller.
    pub generator_data: Place<'tcx>,
}

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

/// Try to interpret this function as an async function.
///
/// If this is an async function it returns the [`Instance`] of the generator,
/// the location where the generator is bound and the type of [`Asyncness`]
/// which in this case is guaranteed to satisfy [`Asyncness::is_async`].
pub fn determine_async<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
) -> Option<(Instance<'tcx>, Location, AsyncType)> {
    let ((generator_def_id, args, loc), asyncness) = if tcx.asyncness(def_id).is_async() {
        (get_async_generator(body), AsyncType::Fn)
    } else {
        (
            try_as_async_trait_function(tcx, def_id, body)?,
            AsyncType::Trait,
        )
    };
    let param_env = tcx.param_env_reveal_all_normalized(def_id);
    let generator_fn =
        utils::try_resolve_function(tcx, generator_def_id.to_def_id(), param_env, args)?;
    Some((generator_fn, loc, asyncness))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AsyncDeterminationResult<T> {
    Resolved(T),
    Unresolvable(String),
    NotAsync,
}

/// Does this instance refer to an `async fn` or `async {}`.
fn is_async_fn_or_block(tcx: TyCtxt, instance: Instance) -> bool {
    // It turns out that the `DefId` of the [`poll`](std::future::Future::poll)
    // impl for an `async fn` or async block is the same as the `DefId` of the
    // generator itself. That means after resolution (e.g. on the `Instance`) we
    // only need to call `tcx.generator_is_async`.
    tcx.generator_is_async(instance.def_id())
}

impl<'tcx, 'mir> LocalAnalysis<'tcx, 'mir> {
    /// Checks whether the function call, described by the unresolved `def_id`
    /// and the resolved instance `resolved_fn` is a call to [`<T as
    /// Future>::poll`](std::future::Future::poll) where `T` is the type of an
    /// `async fn` or `async {}` created generator.
    ///
    /// Resolves the original arguments that constituted the generator.
    pub(crate) fn try_poll_call_kind<'a>(
        &'a self,
        def_id: DefId,
        resolved_fn: Instance<'tcx>,
        original_args: &'a [Operand<'tcx>],
    ) -> AsyncDeterminationResult<CallKind<'tcx>> {
        let lang_items = self.tcx().lang_items();
        if lang_items.future_poll_fn() == Some(def_id)
            && is_async_fn_or_block(self.tcx(), resolved_fn)
        {
            match self.find_async_args(original_args) {
                Ok(poll) => AsyncDeterminationResult::Resolved(CallKind::AsyncPoll(poll)),
                Err(str) => AsyncDeterminationResult::Unresolvable(str),
            }
        } else {
            AsyncDeterminationResult::NotAsync
        }
    }
    /// Given the arguments to a `Future::poll` call, walk back through the
    /// body to find the original future being polled, and get the arguments to the future.
    fn find_async_args<'a>(
        &'a self,
        args: &'a [Operand<'tcx>],
    ) -> Result<AsyncFnPollEnv<'tcx>, String> {
        macro_rules! let_assert {
            ($p:pat = $e:expr, $($arg:tt)*) => {
                let $p = $e else {
                    let msg = format!($($arg)*);
                    return Err(format!(
                        "Abandoning attempt to handle async because pattern {} (line {}) could not be matched to {:?}: {}",
                        stringify!($p),
                        line!(),
                        $e,
                        msg
                    ));
                };
            }
        }
        let get_def_for_op = |op: &Operand<'tcx>| -> Result<Location, String> {
            let_assert!(Some(place) = op.place(), "Arg is not a place");
            let_assert!(
                Some(local) = place.as_local(),
                "Place {place:?} is not a local"
            );
            let_assert!(
                Some(locs) = &self.body_assignments.get(&local),
                "Local has no assignments"
            );
            assert!(locs.len() == 1);
            Ok(locs[0])
        };

        let_assert!(
            Either::Right(Terminator {
                kind: TerminatorKind::Call {
                    args: new_pin_args,
                    ..
                },
                ..
            }) = &self.mono_body.stmt_at(get_def_for_op(&args[0])?),
            "Pinned assignment is not a call"
        );
        debug_assert!(new_pin_args.len() == 1);

        let future_aliases = self
            .aliases(self.tcx().mk_place_deref(new_pin_args[0].place().unwrap()))
            .collect_vec();
        debug_assert!(future_aliases.len() == 1);
        let future = *future_aliases.first().unwrap();

        let_assert!(
          Either::Left(Statement {
            kind: StatementKind::Assign(box (_, Rvalue::Use(future2))),
            ..
          }) = &self.mono_body.stmt_at(get_def_for_op(&Operand::Move(future))?),
          "Assignment to pin::new input is not a statement"
        );

        let_assert!(
            Either::Right(Terminator {
                kind: TerminatorKind::Call {
                    args: into_future_args,
                    ..
                },
                ..
            }) = &self.mono_body.stmt_at(get_def_for_op(future2)?),
            "Assignment to alias of pin::new input is not a call"
        );

        let target = &into_future_args[0];
        let creation_loc = get_def_for_op(target)?;
        let stmt = &self.mono_body.stmt_at(creation_loc);
        let (op, generics, generator_data) = match stmt {
            Either::Right(Terminator {
                kind:
                    TerminatorKind::Call {
                        func, destination, ..
                    },
                ..
            }) => {
                let (op, generics) = self.operand_to_def_id(func).unwrap();
                (Some(op), generics, *destination)
            }
            Either::Left(Statement { kind, .. }) => match kind {
                StatementKind::Assign(box (
                    lhs,
                    Rvalue::Aggregate(box AggregateKind::Generator(def_id, generic_args, _), _args),
                )) => {
                    assert!(self.tcx().generator_is_async(*def_id));
                    (None, *generic_args, *lhs)
                }
                StatementKind::Assign(box (_, Rvalue::Use(target))) => {
                    let generics = self
                        .operand_to_def_id(target)
                        .ok_or_else(|| "Nope".to_string())?
                        .1;
                    (None, generics, target.place().unwrap())
                }
                _ => {
                    panic!("Assignment to into_future input is not a call: {stmt:?}");
                }
            },
            _ => {
                panic!("Assignment to into_future input is not a call: {stmt:?}");
            }
        };

        let async_fn_parent = op
            .map(|def_id| {
                utils::try_resolve_function(
                    self.tcx(),
                    def_id,
                    self.tcx().param_env_reveal_all_normalized(self.def_id),
                    generics,
                )
                .ok_or_else(|| "Instance resolution failed".to_string())
            })
            .transpose()?;

        Ok(AsyncFnPollEnv {
            async_fn_parent,
            creation_loc,
            generator_data,
        })
    }
}
