use std::rc::Rc;

use flowistry_pdg_construction::{body_cache::BodyCache, CallInfo};
use paralegal_spdg::{utils::write_sep, Identifier};
use rustc_hash::FxHashSet;
use rustc_hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc_middle::ty::{
    BoundVariableKind, ClauseKind, ImplPolarity, Instance, ParamEnv, TraitPredicate,
};
use rustc_span::Symbol;
use rustc_type_ir::TyKind;

use crate::{
    ana::Print, ann::db::MarkerDatabase, args::InliningDepth, AnalysisCtrl, Args, MarkerCtx, TyCtxt,
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
            MarkerDatabase::init(tcx, opts, body_cache, included_crates.iter().copied()).into();
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
    pub fn should_inline(&self, info: &CallInfo<'tcx>) -> bool {
        let marker_target = info.async_parent.unwrap_or(info.callee);
        let marker_target_def_id = marker_target.def_id();
        match self.analysis_control.inlining_depth() {
            _ if !self.included_crates.contains(&marker_target_def_id.krate)
                || self.marker_ctx.is_marked(marker_target_def_id) =>
            {
                false
            }
            InliningDepth::Adaptive => self
                .marker_ctx
                .has_transitive_reachable_markers(marker_target),
            InliningDepth::Shallow => false,
            InliningDepth::Unconstrained => true,
        }
    }

    pub fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        &self.marker_ctx
    }

    pub fn ensure_is_safe_to_approximate(&self, original_target: DefId, resolved: Instance<'tcx>) {
        println!("Ensuring approximation safety for {resolved:?}");
        let sess = self.tcx().sess;
        let predicates = self
            .tcx()
            .predicates_of(original_target)
            .instantiate(self.tcx(), resolved.args);
        for (clause, span) in &predicates {
            let err = |s: &str| {
                sess.span_err(
                    span,
                    format!("Cannot verify that non-inlined function is safe due to: {s}"),
                );
            };
            let err_markers = |s: &str, markers: &[Identifier]| {
                if !markers.is_empty() {
                    err(&format!(
                        "{s}: found marker(s) {}",
                        Print(|fmt| write_sep(fmt, ", ", markers, |elem, fmt| write!(
                            fmt,
                            "'{elem}'"
                        )))
                    ));
                }
            };
            let kind = clause.kind();
            for bound in kind.bound_vars() {
                match bound {
                    BoundVariableKind::Ty(t) => err(&format!("bound type {t:?}")),
                    BoundVariableKind::Const | BoundVariableKind::Region(_) => (),
                }
            }

            match kind.skip_binder() {
                ClauseKind::TypeOutlives(_)
                | ClauseKind::WellFormed(_)
                | ClauseKind::ConstArgHasType(..)
                | ClauseKind::ConstEvaluatable(_)
                | ClauseKind::RegionOutlives(_) => {
                    // These predicates do not allow for "code injection" since they do not concern things that can be marked.
                }
                ClauseKind::Projection(p) => {
                    if let Some(t) = p.term.ty() {
                        let markers = self.marker_ctx().deep_type_markers(t);
                        if !markers.is_empty() {
                            let markers = markers.iter().map(|t| t.1).collect::<Box<_>>();
                            err_markers(&format!("type {t:?} is not approximation safe"), &markers);
                        }
                    }
                }
                ClauseKind::Trait(TraitPredicate {
                    polarity: ImplPolarity::Positive,
                    trait_ref,
                }) if !self.tcx().trait_is_auto(trait_ref.def_id) => {
                    let ref_1 = trait_ref.args[0];
                    let Some(self_ty) = ref_1.as_type() else {
                        err("expected self type to be type, got {ref_1:?}");
                        continue;
                    };

                    if self.tcx().is_fn_trait(trait_ref.def_id) {
                        let instance = match self_ty.kind() {
                            TyKind::Closure(id, args) | TyKind::FnDef(id, args) => {
                                Instance::resolve(self.tcx(), ParamEnv::reveal_all(), *id, args)
                            }
                            _ => {
                                err(&format!(
                                "fn-trait instance for {self_ty:?} not being a function of closure"
                            ));
                                continue;
                            }
                        }
                        .unwrap()
                        .unwrap();
                        let markers = self.marker_ctx().get_reachable_markers(instance);
                        if !markers.is_empty() {
                            err_markers(
                                &format!("closure {instance:?} is not approximation safe"),
                                markers,
                            );
                        }
                    } else {
                        self.tcx()
                            .for_each_relevant_impl(trait_ref.def_id, self_ty, |impl_| {
                                for method in self.tcx().associated_item_def_ids(impl_) {
                                    let markers = self.marker_ctx().get_reachable_markers(*method);
                                    if !markers.is_empty() {
                                        err_markers(
                                            &format!("impl {impl_:?} for {self_ty:?}"),
                                            markers,
                                        )
                                    }
                                }
                            })
                    }
                }
                _ => (),
            }
        }
    }
}
