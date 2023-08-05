//! MIR visitor ([`CollectingVisitor`]) that discovers and stores all items of interest.
//!
//! Items of interest is anything annotated with one of the `dfpp::`
//! annotations.
use crate::{consts, desc::*, rust::*, utils::*, HashMap, MarkerCtx};

use hir::{
    def_id::DefId,
    intravisit::{self, FnKind},
    BodyId,
};
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_span::{symbol::Ident, Span, Symbol};

/// Values of this type can be matched against Rust attributes
pub type AttrMatchT = Vec<Symbol>;

/// A mapping of annotations that are attached to function calls.
///
/// XXX: This needs to be adjusted to attach to the actual call site instead of
/// the function `DefId`
pub type CallSiteAnnotations = HashMap<DefId, (Vec<Annotation>, usize)>;

#[allow(clippy::type_complexity)]
/// This visitor traverses the items in the analyzed crate to discover
/// annotations and analysis targets and store them in this struct. After the
/// discovery phase [`Self::analyze`] is used to drive the
/// actual analysis. All of this is conveniently encapsulated in the
/// [`Self::run`] method.
pub struct CollectingVisitor<'tcx> {
    /// Reference to rust compiler queries.
    pub tcx: TyCtxt<'tcx>,
    /// Command line arguments.
    pub opts: &'static crate::Args,
    /// Functions that are annotated with `#[dfpp::analyze]`. For these we will
    /// later perform the analysis
    pub functions_to_analyze: Vec<FnToAnalyze>,

    pub marker_ctx: MarkerCtx<'tcx>,
}

/// A function we will be targeting to analyze with
/// [`CollectingVisitor::handle_target`].
pub struct FnToAnalyze {
    pub name: Ident,
    pub body_id: BodyId,
}

impl FnToAnalyze {
    /// Give me a name that describes this function.
    pub fn name(&self) -> Symbol {
        self.name.name
    }
}

impl<'tcx> CollectingVisitor<'tcx> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        opts: &'static crate::Args,
        marker_ctx: MarkerCtx<'tcx>,
    ) -> Self {
        Self {
            tcx,
            opts,
            functions_to_analyze: vec![],
            marker_ctx,
        }
    }

    /// Does the function named by this id have the `dfpp::analyze` annotation
    fn should_analyze_function(&self, ident: LocalDefId) -> bool {
        self.tcx
            .hir()
            .attrs(self.tcx.local_def_id_to_hir_id(ident))
            .iter()
            .any(|a| a.matches_path(&consts::ANALYZE_MARKER))
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for CollectingVisitor<'tcx> {
    type NestedFilter = OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    /// Finds the functions that have been marked as targets.
    fn visit_fn(
        &mut self,
        kind: FnKind<'tcx>,
        declaration: &'tcx rustc_hir::FnDecl<'tcx>,
        body_id: BodyId,
        _s: Span,
        id: LocalDefId,
    ) {
        match &kind {
            FnKind::ItemFn(name, _, _) | FnKind::Method(name, _)
                if self.should_analyze_function(id) =>
            {
                self.functions_to_analyze.push(FnToAnalyze {
                    name: *name,
                    body_id,
                });
            }
            _ => (),
        }

        // dispatch to recursive walk. This is probably unnecessary but if in
        // the future we decide to do something with nested items we may need
        // it.
        intravisit::walk_fn(self, kind, declaration, body_id, id)
    }
}
