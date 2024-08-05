use std::rc::Rc;

use flowistry_pdg_construction::{body_cache::BodyCache, CallInfo};
use paralegal_spdg::{utils::write_sep, Identifier};
use rustc_hash::FxHashSet;
use rustc_hir::{
    def::DefKind,
    def_id::{CrateNum, DefId, LOCAL_CRATE},
};
use rustc_middle::ty::{
    AssocKind, BoundVariableKind, Clause, ClauseKind, ImplPolarity, Instance, ParamEnv,
    ProjectionPredicate, TraitPredicate, Ty,
};
use rustc_span::{Span, Symbol};
use rustc_type_ir::TyKind;

use crate::{
    ana::Print,
    ann::db::MarkerDatabase,
    args::{FlowModel, InliningDepth},
    AnalysisCtrl, Args, MarkerCtx, TyCtxt,
};

/// The interpretation of marker placement as it pertains to inlining and inline
/// elision.
///
/// [`MarkerCtx`] provides the information on which this judge bases its
/// decisions. It also takes into account whether the respective configuration
/// options have been set.
pub struct InlineJudge<'tcx> {
    marker_ctx: MarkerCtx<'tcx>,
    analysis_control: &'static AnalysisCtrl,
    included_crates: FxHashSet<CrateNum>,
    tcx: TyCtxt<'tcx>,
}

#[derive(strum::AsRefStr)]
pub enum InlineJudgement {
    Inline,
    UseFlowModel(&'static FlowModel),
    NoInline,
}

impl From<bool> for InlineJudgement {
    fn from(value: bool) -> Self {
        if value {
            InlineJudgement::Inline
        } else {
            InlineJudgement::NoInline
        }
    }
}

impl<'tcx> InlineJudge<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body_cache: Rc<BodyCache<'tcx>>, opts: &'static Args) -> Self {
        let included_crate_names = opts
            .anactrl()
            .included()
            .iter()
            .map(|s| Symbol::intern(s))
            .collect::<FxHashSet<_>>();
        let included_crates = tcx
            .crates(())
            .iter()
            .copied()
            .filter(|cnum| included_crate_names.contains(&tcx.crate_name(*cnum)))
            .chain(Some(LOCAL_CRATE))
            .collect::<FxHashSet<_>>();
        let marker_ctx =
            MarkerDatabase::init(tcx, opts, body_cache, included_crates.clone()).into();
        Self {
            marker_ctx,
            included_crates,
            analysis_control: opts.anactrl(),
            tcx,
        }
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn included_crates(&self) -> &FxHashSet<CrateNum> {
        &self.included_crates
    }

    /// Should we perform inlining on this function?
    pub fn should_inline(&self, info: &CallInfo<'tcx, '_>) -> InlineJudgement {
        let marker_target = info.async_parent.unwrap_or(info.callee);
        let marker_target_def_id = marker_target.def_id();
        if let Some(model) = self.marker_ctx().has_flow_model(marker_target_def_id) {
            return InlineJudgement::UseFlowModel(model);
        }
        let is_marked = self.marker_ctx.is_marked(marker_target_def_id);
        let judgement = match self.analysis_control.inlining_depth() {
            _ if !self.included_crates.contains(&marker_target_def_id.krate) || is_marked => {
                InlineJudgement::NoInline
            }
            InliningDepth::Adaptive => self
                .marker_ctx
                .has_transitive_reachable_markers(marker_target)
                .into(),
            InliningDepth::Shallow => InlineJudgement::NoInline,
            InliningDepth::Unconstrained => InlineJudgement::Inline,
        };
        if matches!(judgement, InlineJudgement::NoInline) {
            println!("Ensuring approximate safety of {:?}", info.callee);
            self.ensure_is_safe_to_approximate(info.param_env, info.callee, info.span, !is_marked)
        }
        println!("Judgement for {:?} is {}", info.callee, judgement.as_ref());
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
    ) {
        SafetyChecker {
            tcx: self.tcx(),
            emit_err,
            param_env,
            resolved,
            call_span,
            marker_ctx: self.marker_ctx.clone(),
        }
        .check()
    }
}

struct SafetyChecker<'tcx> {
    tcx: TyCtxt<'tcx>,
    emit_err: bool,
    param_env: ParamEnv<'tcx>,
    resolved: Instance<'tcx>,
    call_span: Span,
    marker_ctx: MarkerCtx<'tcx>,
}

impl<'tcx> SafetyChecker<'tcx> {
    fn err(&self, s: &str, span: Span) {
        let sess = self.tcx.sess;
        let msg = format!("Cannot verify that non-inlined function is safe due to: {s}");
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
        match predicate {
            TraitPredicate {
                polarity: ImplPolarity::Positive,
                trait_ref,
            } if !self.tcx.trait_is_auto(trait_ref.def_id) => {
                let ref_1 = trait_ref.args[0];
                let Some(self_ty) = ref_1.as_type() else {
                    self.err("expected self type to be type, got {ref_1:?}", span);
                    return;
                };

                if self.tcx.is_fn_trait(trait_ref.def_id) {
                    let instance = match self_ty.kind() {
                        TyKind::Closure(id, args) | TyKind::FnDef(id, args) => {
                            Instance::resolve(self.tcx, ParamEnv::reveal_all(), *id, args)
                        }
                        _ => {
                            self.err(
                                &format!(
                                "fn-trait instance for {self_ty:?} not being a function of closure"
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
                            self.check_impl(r#impl, self_ty, span)
                        })
                }
            }
            _ => (),
        }
    }

    fn check_impl(&self, r#impl: DefId, self_ty: Ty<'tcx>, span: Span) {
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

    fn check(&self) {
        let predicates = self
            .tcx
            .predicates_of(self.resolved.def_id())
            .instantiate(self.tcx, self.resolved.args);
        for (clause, span) in &predicates {
            self.check_predicate(clause, span)
        }
    }
}
