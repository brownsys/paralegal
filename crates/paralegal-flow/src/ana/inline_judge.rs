use std::{fmt::Display, rc::Rc};

use flowistry_pdg_construction::{body_cache::BodyCache, CallInfo};
use paralegal_spdg::{utils::write_sep, Identifier};
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_middle::ty::{
    AssocKind, BoundVariableKind, Clause, ClauseKind, ImplPolarity, Instance, ParamEnv,
    ProjectionPredicate, TraitPredicate,
};
use rustc_span::Span;
use rustc_type_ir::TyKind;

use crate::{
    ana::Print,
    ann::db::MarkerDatabase,
    args::{InliningDepth, Stub},
    Args, MarkerCtx, TyCtxt,
};

/// The interpretation of marker placement as it pertains to inlining and inline
/// elision.
///
/// [`MarkerCtx`] provides the information on which this judge bases its
/// decisions. It also takes into account whether the respective configuration
/// options have been set.
pub struct InlineJudge<'tcx> {
    marker_ctx: MarkerCtx<'tcx>,
    opts: &'static Args,
    included_crates: Rc<dyn Fn(CrateNum) -> bool>,
    tcx: TyCtxt<'tcx>,
}

/// Describes the type of inlining to perform
#[derive(strum::AsRefStr)]
pub enum InlineJudgement {
    /// Construct a graph for the called function and merge it
    Inline,
    /// Use a stub instead of the call
    UseStub(&'static Stub),
    /// Abstract the call via type signature
    AbstractViaType(&'static str),
}

impl Display for InlineJudgement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_ref())?;
        match self {
            Self::AbstractViaType(reason) => write!(f, "({reason})")?,
            _ => (),
        }
        Ok(())
    }
}

impl<'tcx> InlineJudge<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body_cache: Rc<BodyCache<'tcx>>, opts: &'static Args) -> Self {
        let included_crates = Rc::new(opts.anactrl().inclusion_predicate(tcx));
        let marker_ctx = MarkerDatabase::init(tcx, opts, body_cache).into();
        Self {
            marker_ctx,
            included_crates,
            opts,
            tcx,
        }
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn is_included(&self, c: CrateNum) -> bool {
        (self.included_crates)(c)
    }

    /// Should we perform inlining on this function?
    pub fn should_inline(&self, info: &CallInfo<'tcx, '_>) -> InlineJudgement {
        let marker_target = info.async_parent.unwrap_or(info.callee);
        let marker_target_def_id = marker_target.def_id();
        if let Some(model) = self.marker_ctx().has_stub(marker_target_def_id) {
            // If we're replacing an async function skip the poll call.
            //
            // I tried to have it replace the poll call only but that didn't seem to work.
            return if info.async_parent.is_some() {
                InlineJudgement::AbstractViaType("async parent of stub")
            } else {
                InlineJudgement::UseStub(model)
            };
        }
        let is_marked = self.marker_ctx.is_marked(marker_target_def_id);
        let judgement = match self.opts.anactrl().inlining_depth() {
            _ if !self.is_included(marker_target_def_id.krate) => {
                InlineJudgement::AbstractViaType("inlining for crate disabled")
            }
            _ if self.tcx().is_foreign_item(marker_target_def_id) => {
                InlineJudgement::AbstractViaType("cannot inline foreign item")
            }
            _ if is_marked => InlineJudgement::AbstractViaType("marked"),
            InliningDepth::Adaptive
                if self
                    .marker_ctx
                    .has_transitive_reachable_markers(marker_target) =>
            {
                InlineJudgement::Inline
            }
            InliningDepth::Adaptive => InlineJudgement::AbstractViaType("adaptive inlining"),
            InliningDepth::Shallow => {
                InlineJudgement::AbstractViaType("shallow inlining configured")
            }
            InliningDepth::Unconstrained => InlineJudgement::Inline,
        };
        if let InlineJudgement::AbstractViaType(reason) = judgement {
            let emit_err = !(is_marked || self.opts.relaxed());
            self.ensure_is_safe_to_approximate(
                info.param_env,
                info.callee,
                info.span,
                emit_err,
                reason,
            )
        }
        judgement
    }

    pub fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        &self.marker_ctx
    }

    pub fn ensure_is_safe_to_approximate(
        &self,
        param_env: ParamEnv<'tcx>,
        resolved: Instance<'tcx>,
        call_span: Span,
        emit_err: bool,
        reason: &'static str,
    ) {
        SafetyChecker {
            tcx: self.tcx(),
            emit_err,
            param_env,
            resolved,
            call_span,
            marker_ctx: self.marker_ctx.clone(),
            reason,
        }
        .check()
    }
}

/// A check for the abstraction safety of a given instance.
///
/// It looks at each trait predicate on the function and how they are
/// instantiated, then checks the methods defined on those traits and whether
/// they may attach markers. Each time a potential marker is found a diagnostic
/// message is emitted.
///
/// The main entrypoint is [`Self::check`].
struct SafetyChecker<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Emit errors if `true`, otherwise emit warnings
    emit_err: bool,
    param_env: ParamEnv<'tcx>,
    /// Instance under scrutiny
    resolved: Instance<'tcx>,
    call_span: Span,
    marker_ctx: MarkerCtx<'tcx>,
    /// Why a call we check wasn't inlined
    reason: &'static str,
}

impl<'tcx> SafetyChecker<'tcx> {
    /// Emit an error or a warning with some preformatted messaging.
    fn err(&self, s: &str, span: Span) {
        let sess = self.tcx.sess;
        let msg = format!(
            "the call to {:?} is not safe to abstract as demanded by '{}', because of: {s}",
            self.resolved, self.reason
        );
        if self.emit_err {
            let mut diagnostic = sess.struct_span_err(span, msg);
            diagnostic.span_note(self.call_span, "Called from here");
            diagnostic.emit();
        } else {
            let mut diagnostic = sess.struct_span_warn(span, msg);
            diagnostic.span_note(self.call_span, "Called from here");
            diagnostic.emit();
        }
    }

    /// Emit an error that mentions the `markers` found
    fn err_markers(&self, s: &str, markers: &[Identifier], span: Span) {
        if !markers.is_empty() {
            self.err(
                &format!(
                    "{s}: found marker(s) {}",
                    Print(|fmt| write_sep(fmt, ", ", markers, |elem, fmt| write!(fmt, "'{elem}'")))
                ),
                span,
            );
        }
    }

    fn check_projection_predicate(&self, predicate: &ProjectionPredicate<'tcx>, span: Span) {
        if let Some(t) = predicate.term.ty() {
            let t = self.tcx.normalize_erasing_regions(self.param_env, t);
            let markers = self.marker_ctx.deep_type_markers(t);
            if !markers.is_empty() {
                let markers = markers.iter().map(|t| t.1).collect::<Box<_>>();
                self.err_markers(
                    &format!("type {t:?} is not approximation safe"),
                    &markers,
                    span,
                );
            }
        }
    }

    fn check_trait_predicate(&self, predicate: &TraitPredicate<'tcx>, span: Span) {
        let TraitPredicate {
            polarity: ImplPolarity::Positive,
            trait_ref,
        } = predicate
        else {
            return;
        };
        // Auto traits are built-in and have no methods to check
        if self.tcx.trait_is_auto(trait_ref.def_id) {
            return;
        }

        let Some(self_ty) = trait_ref.args[0].as_type() else {
            self.err("expected self type to be type, got {ref_1:?}", span);
            return;
        };

        if self.tcx.is_fn_trait(trait_ref.def_id) {
            let instance = match self_ty.kind() {
                TyKind::Closure(id, args) | TyKind::FnDef(id, args) => {
                    Instance::resolve(self.tcx, ParamEnv::reveal_all(), *id, args)
                }
                TyKind::FnPtr(_) => {
                    self.err(&format!("unresolvable function pointer {self_ty:?}"), span);
                    return;
                }
                _ => {
                    self.err(
                        &format!(
                            "fn-trait instance for {self_ty:?} not being a function or closure"
                        ),
                        span,
                    );
                    return;
                }
            }
            .unwrap()
            .unwrap();
            let markers = self.marker_ctx.get_reachable_markers(instance);
            if !markers.is_empty() {
                self.err_markers(
                    &format!("closure {instance:?} is not approximation safe"),
                    markers,
                    span,
                );
            }
        } else {
            self.tcx
                .for_each_relevant_impl(trait_ref.def_id, self_ty, |r#impl| {
                    self.check_impl(r#impl, span)
                })
        }
    }

    fn check_impl(&self, r#impl: DefId, span: Span) {
        for item in self.tcx.associated_items(r#impl).in_definition_order() {
            // NOTE: We don't need to check markers on types here, because they
            // will be checked if there is a method that produces (or consumes)
            // this type.
            match item.kind {
                AssocKind::Fn => {
                    let method = item.def_id;
                    let markers = self.marker_ctx.get_reachable_markers(method);
                    if !markers.is_empty() {
                        self.err_markers(&self.tcx.def_path_str(method), markers, span)
                    }
                }
                AssocKind::Const | AssocKind::Type => (),
            }
        }
    }

    fn check_predicate(&self, clause: Clause<'tcx>, span: Span) {
        let kind = clause.kind();
        for bound in kind.bound_vars() {
            match bound {
                BoundVariableKind::Ty(t) => self.err(&format!("bound type {t:?}"), span),
                BoundVariableKind::Const | BoundVariableKind::Region(_) => (),
            }
        }

        match &kind.skip_binder() {
            ClauseKind::TypeOutlives(_)
            | ClauseKind::WellFormed(_)
            | ClauseKind::ConstArgHasType(..)
            | ClauseKind::ConstEvaluatable(_)
            | ClauseKind::RegionOutlives(_) => {
                // These predicates do not allow for "code injection" since they do not concern things that can be marked.
            }
            ClauseKind::Projection(predicate) => self.check_projection_predicate(predicate, span),
            ClauseKind::Trait(predicate) => self.check_trait_predicate(predicate, span),
        }
    }

    /// Main entry point for the check
    fn check(&self) {
        self.tcx
            .predicates_of(self.resolved.def_id())
            .instantiate(self.tcx, self.resolved.args)
            .into_iter()
            .for_each(|(clause, span)| self.check_predicate(clause, span));
    }
}
