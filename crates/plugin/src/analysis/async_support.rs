use std::rc::Rc;

use either::Either;

use rustc_abi::{FieldIdx, VariantIdx};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, Body, Location, Operand, Place, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{self, GenericArgsRef, Instance, TyCtxt},
};
use rustc_span::{Span, Spanned};

use crate::utils::{ArgSlice, TyAsFnResult, is_async};

use super::pdg::local::LocalAnalysis;
use crate::utils;

/// Describe in which way a function is `async`.
///
/// Critically distinguishes between a normal `async fn` and an
/// `#[async_trait]`.
#[derive(Debug, Clone, Copy)]
pub enum AsyncType {
    Fn,
    Trait,
    Tool,
}

impl AsyncType {
    pub fn describe(&self) -> &'static str {
        match self {
            AsyncType::Fn => "async function",
            AsyncType::Trait => "async trait",
            AsyncType::Tool => "async tool",
        }
    }
}

/// Context for a call to [`Future::poll`](std::future::Future::poll), when
/// called on a future created via an `async fn` or an async block.
pub struct AsyncFnPollEnv<'tcx> {
    /// If the generator came from an `async fn`, then this is that function. If
    /// it is from an async block, this is `None`.
    pub async_fn_parent: Option<Instance<'tcx>>,
    /// A place which carries the runtime value representing the generator in
    /// the caller.
    pub generator_data: Place<'tcx>,
    /// Was this from an `await` desugaring and as a result we can guarantee
    /// that `generator_place` refers directly to the generator? Otherwise the
    /// generator place is (over)approximate.
    pub precise: bool,
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
) -> Option<(DefId, GenericArgsRef<'tcx>, Location)> {
    if !has_async_trait_signature(tcx, def_id) {
        return None;
    }
    let (def_id, generics, loc, _) = find_coroutine_assign(body)?;
    Some((def_id, generics, loc))
}

pub fn match_coroutine_assign<'tcx, 'a>(
    statement: &'a Statement<'tcx>,
) -> Option<(
    DefId,
    GenericArgsRef<'tcx>,
    &'a rustc_index::IndexVec<FieldIdx, Operand<'tcx>>,
)> {
    match &statement.kind {
        StatementKind::Assign(box (
            _,
            Rvalue::Aggregate(box AggregateKind::Coroutine(def_id, generic_args), args),
        )) => Some((*def_id, *generic_args, args)),
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
        matches!(assoc_item.container, ty::AssocContainer::TraitImpl(_))
            && assoc_item.trait_item_def_id().is_some()
            && match_pin_box_dyn_ty(tcx.lang_items(), sig.output().skip_binder())
    } else {
        false
    }
}

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
    let Some(box_t) = t_a.boxed_ty() else {
        return false;
    };
    let ty::TyKind::Dynamic(pred, _) = box_t.kind() else {
        return false;
    };
    pred.iter().any(|p| {
        let ty::ExistentialPredicate::Trait(t) = p.skip_binder() else {
            return false;
        };
        Some(t.def_id) == lang_items.future_trait()
    })
}

fn get_async_generator<'tcx>(body: &Body<'tcx>) -> (DefId, GenericArgsRef<'tcx>, Location) {
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
        Rvalue::Aggregate(box AggregateKind::Coroutine(def_id, generic_args), _args),
    )) = &stmt.kind
    else {
        panic!("Async fn should assign to a generator")
    };
    (*def_id, generic_args, location)
}

// matches std::pin::Pin<std::boxed::Box<dyn std::future::Future<_>>
fn has_async_tool_signature(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    use rustc_hir::def::DefKind;
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return false;
    }
    let sig = tcx.fn_sig(def_id);
    let lang_items = tcx.lang_items();
    let ty::TyKind::Adt(adt_def, inner) = sig.skip_binder().output().skip_binder().kind() else {
        return false;
    };
    if !lang_items.pin_type().is_some_and(|p| p == adt_def.did()) {
        return false;
    }
    let [b_ty] = inner.as_slice() else {
        return false;
    };
    let Some(f_ty) = b_ty.as_type().and_then(ty::Ty::boxed_ty) else {
        return false;
    };
    let ty::TyKind::Dynamic(preds, _) = f_ty.kind() else {
        return false;
    };
    let Some(ty::ExistentialPredicate::Trait(t)) = preds.first().map(|b| b.skip_binder()) else {
        return false;
    };
    lang_items.future_trait().is_some_and(|f| f == t.def_id)
}

/// Find the unique top-level `Aggregate(Coroutine(..))` statement in `body`.
///
/// Returns `None` if `body` has no such statement — e.g. a trait method
/// declared to return `Pin<Box<dyn Future>>` that just forwards a future from
/// another call without constructing its own coroutine. Callers should treat
/// `None` as "this function is not an async wrapper we can peel into a
/// coroutine"; analysis falls back to the body as written.
///
/// Panics if `body` has more than one such statement — that signals a body
/// shape we genuinely don't expect (e.g. multiple top-level `async {}` blocks
/// in the same fn) and we'd rather surface it than silently pick one.
pub fn find_coroutine_assign<'tcx, 'a>(
    body: &'a Body<'tcx>,
) -> Option<(
    DefId,
    GenericArgsRef<'tcx>,
    Location,
    &'a rustc_index::IndexVec<FieldIdx, Operand<'tcx>>,
)> {
    let mut matching_statements =
        body.basic_blocks
            .iter_enumerated()
            .flat_map(|(block, bbdat)| {
                bbdat.statements.iter().enumerate().filter_map(
                    move |(statement_index, statement)| {
                        let (def_id, generics, args) = match_coroutine_assign(statement)?;
                        Some((
                            def_id,
                            generics,
                            Location {
                                block,
                                statement_index,
                            },
                            args,
                        ))
                    },
                )
            })
            .collect::<Vec<_>>();
    match matching_statements.len() {
        0 => None,
        1 => Some(matching_statements.pop().unwrap()),
        n => {
            let def_id = body.source.def_id();
            let mut dump = String::new();
            for (block, bbdat) in body.basic_blocks.iter_enumerated() {
                use std::fmt::Write;
                let _ = writeln!(dump, "  {block:?}:");
                for (i, st) in bbdat.statements.iter().enumerate() {
                    let _ = writeln!(dump, "    [{i}] {:?}", st.kind);
                }
                if let Some(t) = &bbdat.terminator {
                    let _ = writeln!(dump, "    T {:?}", t.kind);
                }
            }
            panic!(
                "find_coroutine_assign: expected at most one `Aggregate(Coroutine(..))` \
                 statement in body of {def_id:?} (span {span:?}), found {n}.\n\
                 body dump:\n{dump}\n\
                 matched locations: {locs:?}",
                span = body.span,
                locs = matching_statements
                    .iter()
                    .map(|(d, _, l, _)| (l, d))
                    .collect::<Vec<_>>(),
            );
        }
    }
}

fn try_as_async_tool<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>, Location)> {
    if !has_async_tool_signature(tcx, def_id) {
        return None;
    }
    let (def_id, gargs, loc, _) = find_coroutine_assign(body)?;
    Some((def_id, gargs, loc))
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
    let ((generator_def_id, args, loc), asyncness) = if is_async(tcx, def_id) {
        (get_async_generator(body), AsyncType::Fn)
    } else if let Some(g) = try_as_async_trait_function(tcx, def_id, body) {
        (g, AsyncType::Trait)
    } else {
        (try_as_async_tool(tcx, def_id, body)?, AsyncType::Tool)
    };
    let typing_env = body.typing_env(tcx).with_post_analysis_normalized(tcx);
    let generator_fn = utils::try_resolve_function(tcx, generator_def_id, typing_env, args)?;
    Some((generator_fn, loc, asyncness))
}

/// Does this instance refer to an `async fn` or `async {}`.
pub fn is_async_fn_or_block(tcx: TyCtxt, instance: Instance) -> bool {
    // It turns out that the `DefId` of the [`poll`](std::future::Future::poll)
    // impl for an `async fn` or async block is the same as the `DefId` of the
    // generator itself. That means after resolution (e.g. on the `Instance`) we
    // only need to call `tcx.generator_is_async`.
    tcx.coroutine_is_async(instance.def_id())
}

impl<'tcx, K> LocalAnalysis<'tcx, '_, K> {
    /// Given the arguments to a `Future::poll` call, walk back through the
    /// body to find the original future being polled, and get the arguments to the future.
    pub fn find_async_args<'a>(
        &'a self,
        resolved_fn: Instance<'tcx>,
        args: &'a [Spanned<Operand<'tcx>>],
        span: Span,
    ) -> Result<AsyncFnPollEnv<'tcx>, String> {
        let precise = self.find_async_args_precise(args);
        if precise.is_ok() || span.desugaring_kind() == Some(rustc_span::DesugaringKind::Await) {
            precise
        } else {
            let parent = self.tcx().parent(resolved_fn.def_id());
            Ok(AsyncFnPollEnv {
                async_fn_parent: is_async(self.tcx(), parent).then(|| {
                    utils::try_resolve_function(
                        self.tcx(),
                        parent,
                        self.param_env,
                        resolved_fn.args,
                    )
                    .unwrap()
                }),
                generator_data: args[0].node.place().unwrap(),
                precise: false,
            })
        }
    }

    fn find_async_args_precise<'a>(
        &'a self,
        args: ArgSlice<'a, 'tcx>,
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
            }) = &self.mono_body.stmt_at(get_def_for_op(&args[0].node)?),
            "Pinned assignment is not a call"
        );
        debug_assert!(new_pin_args.len() == 1);

        let future_aliases = self
            .aliases(
                self.tcx()
                    .mk_place_deref(new_pin_args[0].node.place().unwrap()),
            )
            .collect::<Vec<_>>();
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
        let creation_loc = get_def_for_op(&target.node)?;
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
                    Rvalue::Aggregate(box AggregateKind::Coroutine(def_id, generic_args), _args),
                )) => {
                    assert!(self.tcx().coroutine_is_async(*def_id));
                    (None, *generic_args, *lhs)
                }
                StatementKind::Assign(box (_, Rvalue::Use(target))) => {
                    let generics = match self.operand_to_def_id(target) {
                        TyAsFnResult::Resolved { generic_args, .. } => generic_args,
                        TyAsFnResult::FnPtr => return Err("Function pointer".to_string()),
                        TyAsFnResult::NotAFunction => {
                            return Err("Not a function".to_string());
                        }
                    };
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
                    self.mono_body
                        .typing_env(self.tcx())
                        .with_post_analysis_normalized(self.tcx()),
                    generics,
                )
                .ok_or_else(|| {
                    format!(
                        "Resolving instance {} with generics {generics:?} failed",
                        self.tcx().def_path_debug_str(def_id)
                    )
                })
            })
            .transpose()?;

        Ok(AsyncFnPollEnv {
            async_fn_parent,
            generator_data,
            precise: true,
        })
    }
}
