use std::rc::Rc;

use flowistry_pdg_construction::body_cache::BodyCache;
use rustc_errors::DiagnosticMessage;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::{ann::db::MarkerDatabase, MarkerCtx};

#[derive(Clone)]
pub struct Pctx<'tcx>(Rc<PctxPayload<'tcx>>);

impl<'tcx> Pctx<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, opts: &'static crate::Args) -> Self {
        let body_cache = Rc::new(BodyCache::new(tcx));
        let marker_ctx = MarkerDatabase::init(tcx, opts, body_cache.clone()).into();
        let payload = PctxPayload {
            tcx,
            body_cache,
            opts,
            marker_ctx,
        };
        Self(Rc::new(payload))
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.0.tcx
    }

    pub fn body_cache(&self) -> &Rc<BodyCache<'tcx>> {
        &self.0.body_cache
    }

    pub fn opts(&self) -> &'static crate::Args {
        self.0.opts
    }

    pub fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        &self.0.marker_ctx
    }

    /// Emit an errror or a warning if relaxed.
    pub fn maybe_span_err(&self, span: Span, msg: impl Into<DiagnosticMessage>) {
        if self.opts().relaxed() {
            self.tcx().sess.span_err(span, msg);
        } else {
            self.tcx().sess.span_warn(span, msg);
        }
    }
}

struct PctxPayload<'tcx> {
    tcx: TyCtxt<'tcx>,
    body_cache: Rc<BodyCache<'tcx>>,
    opts: &'static crate::Args,
    marker_ctx: MarkerCtx<'tcx>,
}
