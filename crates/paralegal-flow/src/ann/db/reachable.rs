use crate::{
    ann::db::{InferenceResult, SideEffectReason},
    utils::{ty_of_const, type_for_constructor},
    HashSet,
};
use flowistry::mir::FlowistryInput;
use flowistry_pdg_construction::{
    determine_async,
    utils::{
        handle_shims, is_virtual, try_monomorphize, try_resolve_function, type_as_fn, ShimResult,
    },
};
use paralegal_spdg::Identifier;

use rustc_data_structures::fx::FxHashSet;
use rustc_middle::{
    mir,
    ty::{self, TypingEnv},
};

use std::borrow::Cow;

use super::{MarkerCtx, MaybeMonomorphized};

impl<'tcx> MarkerCtx<'tcx> {
    /// Queries the transitive marker cache.
    pub fn has_transitive_reachable_markers(
        &self,
        res: impl Into<MaybeMonomorphized<'tcx>>,
    ) -> bool {
        !self.get_reachable_markers(res).is_empty()
    }

    pub fn get_inference_result(
        &self,
        res: impl Into<MaybeMonomorphized<'tcx>>,
    ) -> &InferenceResult<'tcx> {
        let empty = &self.db().empty_inference_result;
        let res = res.into();
        let def_id = res.def_id();
        if self.is_marked(def_id) {
            trace!("  Is marked");
            return empty;
        }
        if is_virtual(self.tcx(), def_id) {
            trace!("  Is virtual");
            return empty;
        }
        if self.tcx().is_foreign_item(def_id) {
            trace!("  Is foreign");
            return empty;
        }
        if !(self.0.included_crates)(def_id.krate) {
            trace!("  Is excluded");
            return empty;
        }
        self.db()
            .call_tree_analysis
            .get_maybe_recursive(&res, |_| self.compute_reachable_markers(res))
            .unwrap_or(empty)
    }

    pub fn get_reachable_markers(&self, res: impl Into<MaybeMonomorphized<'tcx>>) -> &[Identifier] {
        &self.get_inference_result(res).reachable_markers
    }

    fn get_reachable_and_self_markers(
        &self,
        res: impl Into<MaybeMonomorphized<'tcx>>,
    ) -> (
        impl Iterator<Item = Identifier> + '_,
        Option<SideEffectReason<'tcx>>,
    ) {
        let res = res.into();
        let mut direct_markers = self
            .combined_markers(res.def_id())
            .map(|m| m.marker)
            .peekable();
        let is_self_marked = direct_markers.peek().is_some();
        if is_self_marked {
            let mut stat = self.borrow_function_marker_stat(res);
            if stat.markers_on_self.is_empty() {
                stat.markers_on_self
                    .extend(self.combined_markers(res.def_id()).map(|m| m.marker));
            }
        }
        let (non_direct, side_effects) = (!is_self_marked)
            .then(|| {
                let prior = self.get_inference_result(res);
                (&prior.reachable_markers, prior.side_effects.clone())
            })
            .unzip();

        (
            direct_markers.chain(non_direct.into_iter().flatten().copied()),
            side_effects.flatten(),
        )
    }

    /// If the transitive marker cache did not contain the answer, this is what
    /// computes it.
    fn compute_reachable_markers(&self, res: MaybeMonomorphized<'tcx>) -> InferenceResult<'tcx> {
        trace!("Computing reachable markers for {res:?}");

        if self.tcx().is_constructor(res.def_id()) {
            let parent = type_for_constructor(self.tcx(), res.def_id());
            return InferenceResult {
                reachable_markers: self
                    .combined_markers(parent)
                    .map(|m| m.marker)
                    .collect::<Box<_>>(),
                side_effects: None,
            };
        }
        let body = self.db().body_cache.get(res.def_id());
        let param_env = TypingEnv::post_analysis(self.tcx(), res.def_id())
            .with_post_analysis_normalized(self.tcx());
        let mono_body = match res {
            MaybeMonomorphized::Monomorphized(res) => Cow::Owned(
                try_monomorphize(
                    res,
                    self.tcx(),
                    param_env,
                    body.body(),
                    self.tcx().def_span(res.def_id()),
                )
                .unwrap(),
            ),
            MaybeMonomorphized::Plain(_) => Cow::Borrowed(body.body()),
        };
        if let Some((async_fn, _, _)) = determine_async(self.tcx(), res.def_id(), &mono_body) {
            self.borrow_function_marker_stat(res).is_async = Some(async_fn);
            return self.get_inference_result(async_fn).clone();
        }
        let mut vis = BodyAnalyzer::new(self.clone(), res, &mono_body, param_env);
        use mir::visit::Visitor;
        vis.visit_body(&mono_body);
        vis.into_inference_result()
    }

    /// Does this terminator carry a marker?
    fn terminator_reachable_markers(
        &self,
        parent: MaybeMonomorphized<'tcx>,
        local_decls: &mir::LocalDecls<'tcx>,
        terminator: &mir::Terminator<'tcx>,
        param_env: ty::TypingEnv<'tcx>,
        expect_resolve: bool,
    ) -> (
        impl Iterator<Item = Identifier> + '_,
        Option<SideEffectReason<'tcx>>,
    ) {
        let mut v = vec![];
        let mut side_effects = None;
        trace!(
            "  Finding reachable markers for terminator {:?}",
            terminator.kind
        );
        let mir::TerminatorKind::Call { func, .. } = &terminator.kind else {
            return (v.into_iter(), side_effects);
        };

        let Some((def_id, gargs)) = func
            .constant()
            .map(ty_of_const)
            .and_then(|t| type_as_fn(self.tcx(), t).to_option())
        else {
            return (
                v.into_iter(),
                Some(SideEffectReason::HiddenFunction(
                    func.ty(local_decls, self.tcx()),
                    terminator.source_info.span,
                )),
            );
        };
        let mut res = if expect_resolve {
            let Some(instance) = try_resolve_function(self.tcx(), def_id, param_env, gargs) else {
                self.span_err(
                    terminator.source_info.span,
                    format!("cannot determine reachable markers, failed to resolve {def_id:?} with {gargs:?}")
                );
                return (v.into_iter(), Some(SideEffectReason::Function(def_id)));
            };
            let new_instance = match handle_shims(
                instance,
                self.tcx(),
                param_env,
                terminator.source_info.span,
            ) {
                ShimResult::IsHandledShim { instance, .. } => instance,
                ShimResult::IsNonHandleableShim => {
                    self.span_err(
                        terminator.source_info.span,
                        format!("cannot determine reachable markers, failed to handle shim {def_id:?} with {gargs:?}")
                    );
                    return (v.into_iter(), Some(SideEffectReason::Function(def_id)));
                }
                ShimResult::IsNotShim => instance,
            };
            MaybeMonomorphized::Monomorphized(new_instance)
        } else {
            MaybeMonomorphized::Plain(def_id)
        };
        trace!(
            "    Checking function {} for markers",
            self.tcx().def_path_debug_str(res.def_id())
        );

        if let Some(model) = self.has_stub(res.def_id()) {
            if let MaybeMonomorphized::Monomorphized(instance) = &mut res {
                if let Ok(new_instance) = model.resolve_alternate_instance(
                    self.tcx(),
                    *instance,
                    param_env,
                    terminator.source_info.span,
                ) {
                    self.borrow_function_marker_stat(res).is_stubbed = Some(new_instance);
                    let rec = self.get_inference_result(res).clone();
                    v.extend(rec.reachable_markers);
                    side_effects = side_effects.or(rec.side_effects);
                    return (v.into_iter(), side_effects);
                }
            } else {
                self.span_err(
                    terminator.source_info.span,
                    "Could not apply stub to an partially resolved function",
                );
            };
            return (v.into_iter(), side_effects);
        }

        let (markers, direct_side_effects) = self.get_reachable_and_self_markers(res);
        v.extend(markers);
        side_effects = side_effects.or(direct_side_effects);

        // We have to proceed differently than graph construction,
        // because we are not given the closure function, instead
        // we are provided the id of the function that creates the
        // future. As such we can't just monomorphize and traverse,
        // we have to find the generator first.
        if let ty::TyKind::Alias(ty::AliasTyKind::Opaque, alias) =
            local_decls[mir::RETURN_PLACE].ty.kind()
            && let ty::TyKind::Coroutine(closure_fn, substs) =
                self.tcx().type_of(alias.def_id).skip_binder().kind()
        {
            trace!("    fits opaque type");
            let async_closure_fn =
                try_resolve_function(self.tcx(), *closure_fn, param_env, substs).unwrap();
            let prior = self.get_inference_result(async_closure_fn);
            v.extend(&prior.reachable_markers);
            side_effects = side_effects.or(prior.side_effects.clone());
            self.borrow_function_marker_stat(res).is_async = Some(async_closure_fn);
        };
        if !v.is_empty() {
            self.borrow_function_marker_stat(parent)
                .calls_with_reachable_markers
                .push((res, terminator.source_info.span));
        }
        (v.into_iter(), side_effects)
    }
}

struct BodyAnalyzer<'tcx, 'b> {
    ctx: MarkerCtx<'tcx>,
    res: MaybeMonomorphized<'tcx>,
    mono_body: &'b mir::Body<'tcx>,
    param_env: ty::TypingEnv<'tcx>,
    found_markers: FxHashSet<Identifier>,
    side_effects: Option<SideEffectReason<'tcx>>,
}

impl<'tcx, 'b> BodyAnalyzer<'tcx, 'b> {
    fn into_inference_result(self) -> InferenceResult<'tcx> {
        InferenceResult {
            reachable_markers: self.found_markers.into_iter().collect(),
            side_effects: self.side_effects,
        }
    }

    fn expect_resolve(&self) -> bool {
        self.res.is_monomorphized()
    }

    fn new(
        ctx: MarkerCtx<'tcx>,
        res: MaybeMonomorphized<'tcx>,
        mono_body: &'b mir::Body<'tcx>,
        param_env: ty::TypingEnv<'tcx>,
    ) -> Self {
        Self {
            ctx,
            res,
            mono_body,
            param_env,
            found_markers: HashSet::default(),
            side_effects: None,
        }
    }
}

impl<'tcx, 'b> mir::visit::Visitor<'tcx> for BodyAnalyzer<'tcx, 'b> {
    fn visit_local_decl(&mut self, l: mir::Local, v: &mir::LocalDecl<'tcx>) {
        let markers = self.ctx.deep_type_markers(v.ty);
        if !markers.is_empty() {
            self.ctx
                .borrow_function_marker_stat(self.res)
                .markers_from_variables
                .push((l, v.ty, markers.iter().map(|v| v.1).collect()));
        }
        self.found_markers.extend(markers.iter().map(|v| v.1));
        self.super_local_decl(l, v);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: mir::Location) {
        let expect_resolve = self.expect_resolve();
        let (markers, side_effects) = self.ctx.terminator_reachable_markers(
            self.res,
            &self.mono_body.local_decls,
            terminator,
            self.param_env,
            expect_resolve,
        );
        self.side_effects = self.side_effects.take().or(side_effects);
        self.found_markers.extend(markers);
        self.super_terminator(terminator, location);
    }
}
