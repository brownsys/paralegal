use std::{fmt::Display, rc::Rc};

use either::Either;
use flowistry_pdg::{CallString, GlobalLocation};
use itertools::Itertools;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_macros::{Decodable, Encodable};
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, Body, Location, Operand, Place, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{GenericArgsRef, Instance, TyCtxt},
};
use rustc_span::Span;

use crate::{
    construct::EmittableError,
    graph::push_call_string_root,
    local_analysis::{CallKind, LocalAnalysis},
    utils, Error, PartialGraph,
};

/// Describe in which way a function is `async`.
///
/// Critically distinguishes between a normal `async fn` and an
/// `#[async_trait]`.
#[derive(Debug, Clone, Copy, Decodable, Encodable)]
pub enum Asyncness {
    No,
    AsyncFn,
    AsyncTrait,
}

impl Asyncness {
    pub fn is_async(self) -> bool {
        !matches!(self, Asyncness::No)
    }
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
    def_id: LocalDefId,
    body: &Body<'tcx>,
) -> Option<(Instance<'tcx>, Location, Asyncness)> {
    let ((generator_def_id, args, loc), asyncness) = if tcx.asyncness(def_id).is_async() {
        (get_async_generator(body), Asyncness::AsyncFn)
    } else {
        (
            try_as_async_trait_function(tcx, def_id.to_def_id(), body)?,
            Asyncness::AsyncTrait,
        )
    };
    let param_env = tcx.param_env_reveal_all_normalized(def_id);
    let generator_fn =
        utils::try_resolve_function(tcx, generator_def_id.to_def_id(), param_env, args)?;
    Some((generator_fn, loc, asyncness))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AsyncDeterminationResult<'tcx, T> {
    Resolved(T),
    Unresolvable(Error<'tcx>),
    NotAsync,
}

#[derive(Debug, Encodable, Decodable, Clone, Hash, Eq, PartialEq)]
pub enum OperandShapeViolation {
    IsNotAPlace,
    IsNotLocal,
    HasNoAssignments,
    WrongNumberOfAssignments(u16),
}

impl Display for OperandShapeViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use OperandShapeViolation::*;
        if let WrongNumberOfAssignments(n) = self {
            return write!(f, "wrong number of assignments, expected 1, got {n}");
        };
        let str = match self {
            IsNotAPlace => "is not a place",
            IsNotLocal => "is not local",
            HasNoAssignments => "is never assigned",
            WrongNumberOfAssignments(..) => unreachable!(),
        };
        f.write_str(str)
    }
}

#[derive(Debug, Encodable, Decodable, Clone, Hash, Eq, PartialEq)]
pub enum AsyncResolutionErr {
    WrongOperandShape {
        span: Span,
        reason: OperandShapeViolation,
    },
    PinnedAssignmentIsNotACall {
        span: Span,
    },
    AssignmentToPinNewIsNotAStatement {
        span: Span,
    },
    AssignmentToAliasOfPinNewInputIsNotACall {
        span: Span,
    },
    AssignmentToIntoFutureInputIsNotACall {
        span: Span,
    },
    ChaseTargetIsNotAFunction {
        span: Span,
    },
}

impl<'tcx> EmittableError<'tcx> for AsyncResolutionErr {
    fn span(&self, _tcx: TyCtxt<'tcx>) -> Option<Span> {
        use AsyncResolutionErr::*;
        match self {
            WrongOperandShape { span, .. }
            | PinnedAssignmentIsNotACall { span }
            | AssignmentToAliasOfPinNewInputIsNotACall { span }
            | AssignmentToIntoFutureInputIsNotACall { span }
            | ChaseTargetIsNotAFunction { span }
            | AssignmentToPinNewIsNotAStatement { span } => Some(*span),
        }
    }

    fn msg(&self, _tcx: TyCtxt<'tcx>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use AsyncResolutionErr::*;
        if let WrongOperandShape { reason, .. } = self {
            return write!(f, "operator has an unexpected shape: {reason}");
        }
        f.write_str(match self {
            PinnedAssignmentIsNotACall { .. } => "pinned assignment is not a call",
            AssignmentToPinNewIsNotAStatement { .. } => "assignment to Pin::new is not a statement",
            AssignmentToAliasOfPinNewInputIsNotACall { .. } => {
                "assignment to Pin::new input is not a call"
            }
            AssignmentToIntoFutureInputIsNotACall { .. } => {
                "assignment to into_future input is not a call"
            }
            ChaseTargetIsNotAFunction { .. } => "chase target is not a function",
            WrongOperandShape { .. } => unreachable!(),
        })
    }
}

impl<'tcx, 'a> LocalAnalysis<'tcx, 'a> {
    pub(crate) fn try_handle_as_async(
        &self,
    ) -> Result<Option<PartialGraph<'tcx>>, Vec<Error<'tcx>>> {
        let Some((generator_fn, location, asyncness)) =
            determine_async(self.tcx(), self.def_id, &self.body)
        else {
            return Ok(None);
        };

        let Some(g) = self.memo.construct_for(generator_fn)? else {
            return Ok(None);
        };
        let gloc = GlobalLocation {
            function: self.def_id.to_def_id(),
            location: flowistry_pdg::RichLocation::Location(location),
        };
        let mut new_g = push_call_string_root(g, gloc);
        //let g_generics = std::mem::replace(&mut new_g.graph.generics, self.generic_args());
        new_g.asyncness = asyncness;
        new_g.monos.insert(CallString::single(gloc), new_g.generics);
        Ok(Some(new_g))
    }

    pub(crate) fn try_poll_call_kind<'b>(
        &'b self,
        def_id: DefId,
        original_args: &'b [Operand<'tcx>],
        span: Span,
    ) -> AsyncDeterminationResult<'tcx, CallKind<'tcx>> {
        let lang_items = self.tcx().lang_items();
        if lang_items.future_poll_fn() == Some(def_id) {
            match self.find_async_args(original_args, span) {
                Ok((fun, loc, args)) => {
                    AsyncDeterminationResult::Resolved(CallKind::AsyncPoll(fun, loc, args))
                }
                Err(str) => AsyncDeterminationResult::Unresolvable(str),
            }
        } else {
            AsyncDeterminationResult::NotAsync
        }
    }
    /// Given the arguments to a `Future::poll` call, walk back through the
    /// body to find the original future being polled, and get the arguments to the future.
    fn find_async_args<'b>(
        &'b self,
        args: &'b [Operand<'tcx>],
        call_span: Span,
    ) -> Result<(Instance<'tcx>, Location, Place<'tcx>), Error<'tcx>> {
        macro_rules! async_err {
            ($msg:expr) => {
                return Err(Error::AsyncResolutionErr($msg))
            };
        }
        macro_rules! let_assert {
            ($p:pat = $e:expr, $msg:expr) => {
                let $p = $e else {
                    async_err!($msg);
                };
            };
        }
        let get_def_for_op = |op: &Operand<'tcx>| -> Result<Location, Error> {
            let mk_err = |reason| AsyncResolutionErr::WrongOperandShape {
                span: call_span,
                reason,
            };
            let_assert!(
                Some(place) = op.place(),
                mk_err(OperandShapeViolation::IsNotAPlace)
            );
            let_assert!(
                Some(local) = place.as_local(),
                mk_err(OperandShapeViolation::IsNotLocal)
            );
            let_assert!(
                Some(locs) = &self.body_assignments.get(&local),
                mk_err(OperandShapeViolation::HasNoAssignments)
            );
            if locs.len() != 1 {
                async_err!(mk_err(OperandShapeViolation::WrongNumberOfAssignments(
                    locs.len() as u16,
                )));
            }
            Ok(locs[0])
        };

        let_assert!(
            Either::Right(Terminator {
                kind: TerminatorKind::Call {
                    args: new_pin_args,
                    ..
                },
                ..
            }) = &self.body.stmt_at(get_def_for_op(&args[0])?),
            AsyncResolutionErr::PinnedAssignmentIsNotACall { span: call_span }
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
          }) = &self.body.stmt_at(get_def_for_op(&Operand::Move(future))?),
          AsyncResolutionErr::AssignmentToPinNewIsNotAStatement { span: call_span }
        );

        let_assert!(
            Either::Right(Terminator {
                kind: TerminatorKind::Call {
                    args: into_future_args,
                    ..
                },
                ..
            }) = &self.body.stmt_at(get_def_for_op(future2)?),
            AsyncResolutionErr::AssignmentToAliasOfPinNewInputIsNotACall { span: call_span }
        );

        let mut chase_target = Err(&into_future_args[0]);

        while let Err(target) = chase_target {
            let async_fn_call_loc = get_def_for_op(target)?;
            let stmt = &self.body.stmt_at(async_fn_call_loc);
            chase_target = match stmt {
                Either::Right(Terminator {
                    kind:
                        TerminatorKind::Call {
                            func, destination, ..
                        },
                    ..
                }) => {
                    let (op, generics) = self.operand_to_def_id(func).unwrap();
                    Ok((op, generics, *destination, async_fn_call_loc))
                }
                Either::Left(Statement { kind, .. }) => match kind {
                    StatementKind::Assign(box (
                        lhs,
                        Rvalue::Aggregate(
                            box AggregateKind::Generator(def_id, generic_args, _),
                            _args,
                        ),
                    )) => Ok((*def_id, *generic_args, *lhs, async_fn_call_loc)),
                    StatementKind::Assign(box (_, Rvalue::Use(target))) => {
                        let Some((op, generics)) = self.operand_to_def_id(target) else {
                            async_err!(AsyncResolutionErr::ChaseTargetIsNotAFunction {
                                span: call_span
                            })
                        };
                        Ok((op, generics, target.place().unwrap(), async_fn_call_loc))
                    }
                    _ => {
                        async_err!(AsyncResolutionErr::AssignmentToIntoFutureInputIsNotACall {
                            span: call_span,
                        });
                    }
                },
                _ => {
                    async_err!(AsyncResolutionErr::AssignmentToIntoFutureInputIsNotACall {
                        span: call_span,
                    });
                }
            };
        }

        let (op, generics, calling_convention, async_fn_call_loc) = chase_target.unwrap();

        let resolution = utils::try_resolve_function(
            self.tcx(),
            op,
            self.tcx().param_env_reveal_all_normalized(self.def_id),
            generics,
        )
        .ok_or_else(|| Error::instance_resolution_failed(op, generics, call_span))?;

        Ok((resolution, async_fn_call_loc, calling_convention))
    }
}
