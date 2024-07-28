//! MIR visitor ([`CollectingVisitor`]) that populates the [`MarkerDatabase`]
//! and discovers functions marked for analysis.
//!
//! Essentially this discovers all local `paralegal_flow::*` annotations.

use std::rc::Rc;

use crate::{
    ana::SPDGGenerator, ann::db::MarkerDatabase, desc::*, stats::Stats, sym_vec, utils::*,
};

use flowistry_pdg_construction::body_cache::BodyCache;
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::{
    def_id::{LocalDefId, LOCAL_CRATE},
    intravisit::{self, FnKind},
    BodyId,
};
use rustc_middle::{hir::nested_filter::OnlyBodies, ty::TyCtxt};
use rustc_span::{symbol::Ident, Span, Symbol};

use anyhow::Result;

use self::resolve::expect_resolve_string_to_def_id;

/// Values of this type can be matched against Rust attributes
pub type AttrMatchT = Vec<Symbol>;

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
    /// Functions that are annotated with `#[paralegal_flow::analyze]`. For these we will
    /// later perform the analysis
    pub functions_to_analyze: Vec<FnToAnalyze>,

    stats: Stats,

    pub marker_ctx: MarkerDatabase<'tcx>,
    body_cache: Rc<BodyCache<'tcx>>,
    /// This will match the annotation `#[paralegal_flow::analyze]` when using
    /// [`MetaItemMatch::match_extract`](crate::utils::MetaItemMatch::match_extract)
    analyze_marker: AttrMatchT,
}

/// A function we will be targeting to analyze with
/// [`CollectingVisitor::handle_target`].
pub struct FnToAnalyze {
    pub name: Ident,
    pub def_id: LocalDefId,
}

impl FnToAnalyze {
    /// Give me a name that describes this function.
    pub fn name(&self) -> Symbol {
        self.name.name
    }
}

impl<'tcx> CollectingVisitor<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, opts: &'static crate::Args, stats: Stats) -> Self {
        let functions_to_analyze = opts
            .anactrl()
            .selected_targets()
            .iter()
            .filter_map(|path| {
                let def_id = expect_resolve_string_to_def_id(tcx, path, opts.relaxed())?;
                if !def_id.is_local() {
                    tcx.sess.span_err(tcx.def_span(def_id), "found an external function as analysis target. Analysis targets are required to be local.");
                    return None;
                }
                Some(FnToAnalyze {
                    def_id: def_id.as_local()?,
                    name: tcx.opt_item_ident(def_id).unwrap(),
                })
            })
            .collect();
        let included_crate_names = opts
            .anactrl()
            .included()
            .iter()
            .map(|s| Symbol::intern(s))
            .collect::<HashSet<_>>();
        let included_crates = tcx
            .crates(())
            .iter()
            .copied()
            .filter(|cnum| included_crate_names.contains(&tcx.crate_name(*cnum)))
            .chain(Some(LOCAL_CRATE))
            .collect::<FxHashSet<_>>();
        let included_crates_copy = included_crates.clone();
        let body_cache = Rc::new(BodyCache::new(tcx, move |krate| {
            included_crates.contains(&krate)
        }));
        let marker_ctx = MarkerDatabase::init(
            tcx,
            opts,
            body_cache.clone(),
            included_crates_copy.into_iter(),
        );
        Self {
            tcx,
            opts,
            functions_to_analyze,
            marker_ctx,
            stats,
            analyze_marker: sym_vec!["paralegal_flow", "analyze"],
            body_cache,
        }
    }

    /// After running the discovery with `visit_all_item_likes_in_crate`, create
    /// the read-only [`SPDGGenerator`] upon which the analysis will run.
    fn into_generator(self) -> SPDGGenerator<'tcx> {
        SPDGGenerator::new(
            self.marker_ctx.into(),
            self.opts,
            self.tcx,
            self.stats,
            self.body_cache,
        )
    }

    /// Driver function. Performs the data collection via visit, then calls
    /// [`Self::analyze`] to construct the Forge friendly description of all
    /// endpoints.
    pub fn run(mut self) -> Result<ProgramDescription> {
        let tcx = self.tcx;
        tcx.hir().visit_all_item_likes_in_crate(&mut self);
        let targets = std::mem::take(&mut self.functions_to_analyze);
        self.into_generator().analyze(targets)
    }

    /// Does the function named by this id have the `paralegal_flow::analyze` annotation
    fn should_analyze_function(&self, ident: LocalDefId) -> bool {
        self.tcx
            .hir()
            .attrs(self.tcx.local_def_id_to_hir_id(ident))
            .iter()
            .any(|a| a.matches_path(&self.analyze_marker))
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
                    def_id: id,
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
