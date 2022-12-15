//! Main analysis pass which proceeds as follows:
//!
//! 1. The HIR visitor [`CollectingVisitor`] traverses the HIR and collects
//!    annotated entities.
//! 2. [`CollectingVisitor::analyze`] is called, which initiates a dataflow
//!    analysis on every [`mir::Body`] that was annotated with
//!    `#[dfpp::analyze]` and performs the following steps
//!
//!    1. Create a [`GlobalFlowConstructor`]
//!    2. The constructor recursively creates finely granular flow graphs
//!       ([`GlobalFlowGraph`]) for callees using information it gets by running
//!       flowistry's dataflow analysis on each Body. Then it inlines them into
//!       the caller using a [`FunctionInliner`] (in
//!       [`GlobalFlowConstructor::compute_granular_global_flows`](GlobalFlowConstructor::compute_granular_global_flows))
//!    3. Reduce the inlined, granular graph for the target function to a
//!       [`CallOnlyFlow`] (on
//!       [`compute_call_only_flow`](GlobalFlowConstructor::compute_call_only_flow))
//!    4. Transform the call-only-flow into a [`Ctrl`] description by adding
//!       information about annotated entities (in
//!       [`CollectingVisitor::handle_target`]
//!
//! 3. Combine the [`Ctrl`] graphs into one [`ProgramDescription`]

use std::{
    borrow::{Borrow, Cow},
    cell::RefCell,
    rc::Rc,
};

use crate::{
    consts, dbg, desc::*, ir::*, rust::*, sah::HashVerifications, utils::*, Either, HashMap,
    HashSet,
};

use hir::{
    def_id::DefId,
    hir_id::HirId,
    intravisit::{self, FnKind},
    BodyId,
};
use mir::{Location, Place, Terminator, TerminatorKind};
use rustc_borrowck::BodyWithBorrowckFacts;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{hir::nested_filter::OnlyBodies, ty::RegionKind};
use rustc_span::{symbol::Ident, Span, Symbol};

use flowistry::{
    indexed::IndexSet,
    infoflow::{FlowAnalysis, FlowDomain, NonTransitiveFlowDomain},
    mir::{borrowck_facts, engine::AnalysisResults, utils::PlaceExt},
};

/// Values of this type can be matched against Rust attributes
pub type AttrMatchT = Vec<Symbol>;

/// A mapping of annotations that are attached to function calls.
///
/// XXX: This needs to be adjusted to attach to the actual call site instead of
/// the function `DefId`
type CallSiteAnnotations = HashMap<DefId, (Vec<Annotation>, usize)>;

/// This function is wholesale lifted from flowistry's recursive analysis. Edits
/// that have been made are just to lift it from a lambda to a top-level
/// function.
///
/// What this function does is relate [`Place`] from the body of a callee to a
/// `Place` in the body of the caller. The most simple example would be one
/// where it relates the formal parameter of a function to the actual call
/// argument as follows. (Shown as MIR)
///
/// ```plain
/// fn callee(_1) {
///   let _2 = ...;
///   ...
/// }
/// fn caller() {
///   ...
///   let _3 = ...;
///   callee(_3)
/// }
/// ```
///
/// Here `translate_child_to_parent(_1) == Some(_3)`. This only works for places
/// that are actually related to the parent, e.g. `translate_child_to_parent(_2)
/// == None` in the example.
///
/// This function does more sophisticated mapping as well through references,
/// derefs and fields. However in all honesty I haven't bothered (yet) to
/// understand its precise capabilities, which should be documented here.
pub fn translate_child_to_parent<'tcx>(
    tcx: TyCtxt<'tcx>,
    parent_local_def_id: LocalDefId,
    args: &[Option<mir::Place<'tcx>>],
    destination: Option<(mir::Place<'tcx>, mir::BasicBlock)>,
    child: mir::Place<'tcx>,
    mutated: bool,
    body: &mir::Body<'tcx>,
    parent_body: &mir::Body<'tcx>,
) -> Option<mir::Place<'tcx>> {
    use flowistry::mir::utils::PlaceExt;
    use mir::HasLocalDecls;
    use mir::ProjectionElem;
    if child.local == mir::RETURN_PLACE && child.projection.len() == 0 {
        if child.ty(body.local_decls(), tcx).ty.is_unit() {
            return None;
        }

        if let Some((dst, _)) = destination {
            return Some(dst);
        }
    }

    if !child.is_arg(body) || (mutated && !child.is_indirect()) {
        return None;
    }

    // For example, say we're calling f(_5.0) and child = (*_1).1 where
    // .1 is private to parent. Then:
    //    parent_toplevel_arg = _5.0
    //    parent_arg_projected = (*_5.0).1
    //    parent_arg_accessible = (*_5.0)

    let parent_toplevel_arg = args[child.local.as_usize() - 1]?;

    let mut projection = parent_toplevel_arg.projection.to_vec();
    let mut ty = parent_toplevel_arg.ty(parent_body.local_decls(), tcx);
    let parent_param_env = tcx.param_env(parent_local_def_id);
    for elem in child.projection.iter() {
        ty = ty.projection_ty_core(tcx, parent_param_env, &elem, |_, field, _| {
            ty.field_ty(tcx, field)
        });
        let elem = match elem {
            ProjectionElem::Field(field, _) => ProjectionElem::Field(field, ty.ty),
            elem => elem,
        };
        projection.push(elem);
    }

    let parent_arg_projected = Place::make(parent_toplevel_arg.local, &projection, tcx);
    Some(parent_arg_projected)
}

/// Bundles together data needed for the global flow construction. The idea is
/// you construct this with [`Self::new`] then call
/// [`Self::compute_granular_global_flows`] and then
/// [`Self::compute_call_only_flow`] on the result, then discard this struct.
pub struct GlobalFlowConstructor<'tcx, 'g, 'a, P: InlineSelector + Clone> {
    // Configuration
    /// Command line and environment options that control analysis behavior (for
    /// us and for flowistry).
    analysis_opts: &'a crate::AnalysisCtrl,
    /// Command line and environment options that control debug output.
    dbg_opts: &'a crate::DbgArgs,
    /// A selector that controls which functions are inlined, both in our code
    /// as well as which functions are recursed into in flowistry. See
    /// [`InlineSelector`] for more information.
    inline_selector: P,

    // Allocators
    /// Rustc query interface
    tcx: TyCtxt<'tcx>,
    /// Global location interner
    gli: GLI<'g>,

    // Memoization
    /// Memoization of intermediate analyses (see [`FunctionFlows`]
    /// documentation for more)
    function_flows: FunctionFlows<'tcx, 'g>,
}

/// This essentially describes a closure that determines for a given
/// [`LocalDefId`] if it should be inlined. Originally this was in fact done by
/// passing a closure, but it couldn't properly satisfy the type checker,
/// because the selector has to be stored in `fluid_let` variable, which is a
/// dynamically scoped variable. This means that the type needs to be valid for
/// a static lifetime, which I believe closures are not.
///
/// In particular the way that this works is that values of this interface are
/// then wrapped with [`RecurseSelector`], which is a flowistry interface that
/// satisfies [`flowistry::extensions::RecurseSelector`]. The wrapper then
/// simply dispatches to the [`InlineSelector`].
///
/// The reason for the two tiers of selectors is that
///
/// - Flowsitry is a separate crate and so I wanted a way to control it that
///   decouples from the specifics of dfpp
/// - We use the selectors to skip functions with annotations, but I wanted to
///   keep the construction of inlined flow graphs agnostic to any notion of
///   annotations. Those are handled by the [`CollectingVisitor`]
///
/// The only implementation currently in use for this is
/// [`SkipAnnotatedFunctionSelector`].
pub trait InlineSelector: 'static {
    fn should_inline(&self, tcx: TyCtxt, did: LocalDefId) -> bool;
}

impl<T: InlineSelector> InlineSelector for Rc<T> {
    fn should_inline(&self, tcx: TyCtxt, did: LocalDefId) -> bool {
        self.as_ref().should_inline(tcx, did)
    }
}

/// A [`flowistry::extensions::RecurseSelector`] that disables recursion if
/// either
///
/// 1. `inline_disabled` has been set (this is usually coming from
///    `crate::AnalysisCtrl::no_recursive_analysis`)
/// 2. The wrapped [`InlineSelector`] returns `false` for the [`LocalDefId`] of
///    the called function.
/// 3. The terminator is not a function call
/// 4. The function being called cannot be statically determined
///
/// The last two are incidental and also simultaneously enforced by flowistry.
struct RecurseSelector {
    inline_disabled: bool,
    inline_selector: Box<dyn InlineSelector>,
}

impl flowistry::extensions::RecurseSelector for RecurseSelector {
    fn is_selected<'tcx>(&self, tcx: TyCtxt<'tcx>, tk: &TerminatorKind<'tcx>) -> bool {
        if self.inline_disabled {
            return false;
        }
        if let Ok(fn_and_args) = tk.as_fn_and_args() {
            if let Some(hir::Node::Item(hir::Item { def_id, .. })) =
                tcx.hir().get_if_local(fn_and_args.0)
            {
                return self.inline_selector.should_inline(tcx, *def_id);
            }
        }
        false
    }
}

impl<'tcx, 'g, 'a, P: InlineSelector + Clone> GlobalFlowConstructor<'tcx, 'g, 'a, P> {
    fn new(
        analysis_opts: &'a crate::AnalysisCtrl,
        dbg_opts: &'a crate::DbgArgs,
        tcx: TyCtxt<'tcx>,
        gli: GLI<'g>,
        inline_selector: P,
    ) -> Self {
        Self {
            analysis_opts,
            dbg_opts,
            tcx,
            gli,
            function_flows: RefCell::new(HashMap::new()),
            inline_selector,
        }
    }

    /// This does the same as [`RecurseSelector`]. It's kind of difficult to
    /// reuse the recurse selector (because it gets moved into a `fluid_let` to
    /// control flowistry recursion), hence this reimplementation here.
    fn should_inline(&self, did: LocalDefId) -> bool {
        !self.analysis_opts.no_recursive_analysis
            && self.inline_selector.should_inline(self.tcx, did)
    }

    /// Find or compute the finely granular flow for the function that this
    /// terminator calls. If successful returns
    ///
    /// 1. The computed flow
    /// 2. The id of the body of the called function
    /// 3. The body of the called function
    /// 4. The arguments to the called function (like [`AsFnAndArgs`] does).
    /// 5. The return place mentioned in the terminator (like [`AsFnAndArgs`]
    ///    does)
    ///
    /// This function fails if
    ///
    /// - The terminator is not a function call
    /// - The called function cannot be statically determined (see
    ///   [`AsFnAndArgs`])
    /// - The called function is not from the local crate
    /// - [`Self::should_inline`] returned `false` for the defid of the called
    ///   function
    /// - This is a recursive call. Note that this does not only apply for
    ///   direct recursive calls, e.g. `foo` calls `foo`, but also mutual
    ///   recursion e.g. `foo` calls `bar` which calls `foo`.
    ///
    /// The error message will indicate which of these cases occurred.
    fn inner_flow_for_terminator(
        &self,
        t: &mir::Terminator<'tcx>,
    ) -> Result<
        (
            Rc<FunctionFlow<'tcx, 'g>>,
            BodyId,
            &'tcx mir::Body<'tcx>,
            Vec<Option<mir::Place<'tcx>>>,
            Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        ),
        &'static str,
    > {
        t.as_fn_and_args().and_then(|(p, args, dest)| {
            let node = self.tcx.hir().get_if_local(p).ok_or("non-local node")?;
            let (_callee_id, callee_local_id, callee_body_id) = node_as_fn(&node)
                .unwrap_or_else(|| panic!("Expected local function node, got {node:?}"));
            let () = if self.should_inline(*callee_local_id) {
                Ok(())
            } else {
                Err("Inline selector was false")
            }?;
            let inner_flow = self
                .compute_granular_global_flows(*callee_body_id)
                .ok_or("is recursive")?;
            let body = borrowck_facts::get_body_with_borrowck_facts(self.tcx, *callee_local_id)
                .simplified_body();
            Ok((inner_flow, *callee_body_id, body, args, dest))
        })
    }

    /// Computes a granular, inlined flow for the body of the `root_function` id
    /// provided. The granular flow contains all locations in this body,
    /// including those that reference statements and non-call terminators. See
    /// also the documentation for [`FunctionFlow`].
    ///
    /// The main work of transforming the body is done by the [`FunctionInliner`]
    /// struct which, similar to the `GlobalFlowConstructor` bundles together
    /// read-only information and mutable memoization state.
    ///
    /// The computation is memoized in `self.function_flows` and calling this
    /// function will immediately return a previous result, if such a result
    /// exists.
    ///
    /// This function returns `None` if this is a recursive call, e.g. if
    /// `root_function` calls itself somewhere in its call chain. Note that this
    /// means that even if this function is recursive a granular flow *will be
    /// computed*, but only for the outermost call, the recursive call on the
    /// inside will be approximated by its type.
    ///
    /// XXX(Justus): I am actually not sure what the implications of that
    /// approximation are for labels.
    fn compute_granular_global_flows(
        &self,
        root_function: BodyId,
    ) -> Option<Rc<FunctionFlow<'tcx, 'g>>> {
        if let Some(inner) = self.function_flows.borrow().get(&root_function) {
            // `inner` is `Option<...>` here which is deliberate. Not only does this
            // mean that we memoize this expensive inlining computation, but also we
            // avoid recursion. Before we start computing we insert `None` for our
            // own id, and so if a recursion (even a mutual one) occurs it will
            // encounter the `None` and abstract the function instead of inlining
            // it. This might not be the best way to handel recursion though.
            return inner.clone();
        };
        let local_def_id = self.tcx.hir().body_owner_def_id(root_function);

        let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(self.tcx, local_def_id);
        let body = body_with_facts.simplified_body();
        let from_flowistry = {
            use flowistry::extensions::{
                fluid_set, ContextMode, EvalMode, EVAL_MODE, RECURSE_SELECTOR,
            };
            let mut eval_mode = EvalMode::default();
            if !self.analysis_opts.no_recursive_analysis && self.analysis_opts.recursive_flowistry {
                eval_mode.context_mode = ContextMode::Recurse;
            }
            fluid_set!(EVAL_MODE, eval_mode);
            let recurse_selector = Box::new(RecurseSelector {
                inline_disabled: self.analysis_opts.no_recursive_analysis,
                inline_selector: Box::new(self.inline_selector.clone()) as Box<dyn InlineSelector>,
            })
                as Box<dyn flowistry::extensions::RecurseSelector>;
            fluid_set!(RECURSE_SELECTOR, recurse_selector);
            flowistry::infoflow::compute_flow_nontransitive(
                self.tcx,
                root_function,
                body_with_facts,
            )
        };

        // Make sure we terminate on recursion
        self.function_flows.borrow_mut().insert(root_function, None);

        let mut inliner = FunctionInliner {
            from_flowistry: &from_flowistry,
            body,
            local_def_id,
            root_function,
            flow_constructor: self,
            //under_construction: RefCell::new(GlobalFlowGraph::new()),
            under_construction: GlobalFlowGraph::new(),
        };

        use mir::visit::Visitor;

        inliner.visit_body(&body);

        self.function_flows.borrow_mut().insert(
            root_function,
            Some(Rc::new(FunctionFlow {
                flow: inliner.under_construction, //.into_inner(),
                analysis: from_flowistry,
            })),
        );
        Some(
            self.function_flows.borrow()[&root_function]
                .as_ref()
                .unwrap()
                .clone(),
        )
    }

    /// Filters the graph `g` for only locations that are function calls while
    /// preserving connections between those locations by flattening transitive
    /// connections via statements between them.
    ///
    /// This is the canonical way for computing a [`CallOnlyFlow`] and supposed to
    /// be called after/on the result of [`Self::compute_granular_global_flows`].
    fn compute_call_only_flow(&self, g: &GlobalFlowGraph<'tcx, 'g>) -> CallOnlyFlow<'g> {
        debug!(
            "Shrinking global flow graph with {} states",
            g.location_states.len()
        );

        let tcx = self.tcx;

        g.location_states
            .iter()
            .filter_map(|(loc, deps)| {
                if deps.is_translated() {
                    // Skip locations that are only there to translate places
                    // on function boundaries.
                    return None;
                }
                let (inner_location, inner_body) = loc.innermost_location_and_body();
                let (args, _) =
                    Keep::from_location(tcx, inner_body, inner_location, loc.is_at_root())
                        .into_keep()?;
                let flows_borrow = self.function_flows.borrow();
                // Gets the `Aliases` struct for `inner_body` that flowistry has computed for us earlier.
                let ref aliases = flows_borrow
                    .get(&inner_body)
                    .unwrap()
                    .as_ref()
                    .unwrap()
                    .analysis
                    .analysis
                    .aliases;
                let deep_deps_for = |p: mir::Place<'tcx>| {
                    deep_dependencies_of(
                        tcx,
                        aliases,
                        *loc,
                        g,
                        p,
                        self.analysis_opts.use_reachable_values_in_dfs(),
                    )
                };
                Some((
                    *loc,
                    CallDeps {
                        input_deps: args
                            .into_iter()
                            .map(|p| p.map_or_else(|| HashSet::new(), deep_deps_for))
                            .collect(),
                        ctrl_deps: HashSet::new(),
                    },
                ))
            })
            .collect()
    }
}

use ty::RegionVid;

struct ComputeCallObligations<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body: &'a mir::Body<'tcx>,
    result: HashSet<(usize, RegionVid)>,
    terminator_index: usize,
    largest_vid: RegionVid,
}

impl<'tcx, 'a> ComputeCallObligations<'tcx, 'a> {
    fn new(tcx: TyCtxt<'tcx>, body: &'a mir::Body<'tcx>) -> Self {
        Self {
            tcx,
            body,
            result: HashSet::new(),
            terminator_index: 0,
            largest_vid: RegionVid::from_usize(0),
        }
    }

    fn result(&self) -> HashSet<(RegionVid, RegionVid)> {
        self.result
            .iter()
            .flat_map(|&(idx, v)| {
                let mut new_vid = self.largest_vid;
                <RegionVid as rustc_index::vec::Idx>::increment_by(&mut new_vid, idx);
                [(new_vid, v), (v, new_vid)]
            })
            .collect()
    }

    fn handle_vid(&mut self, vid: RegionVid) {
        self.largest_vid = vid.max(self.largest_vid);
    }
}

struct RegionCollector {
    result: HashSet<RegionVid>,
}

impl<'tcx> ty::fold::TypeVisitor<'tcx> for RegionCollector {
    fn visit_region(&mut self, r: ty::Region<'tcx>) -> std::ops::ControlFlow<Self::BreakTy> {
        if let RegionKind::ReVar(v) = r.kind() {
            self.result.insert(v);
        }
        std::ops::ControlFlow::Continue(())
    }
}

impl<'tcx, 'a> mir::visit::Visitor<'tcx> for ComputeCallObligations<'tcx, 'a> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        debug!("Visiting terminator {:?}", terminator.kind);
        if let TerminatorKind::Call {
            args, destination, ..
        } = &terminator.kind
        {
            let mut collector = RegionCollector {
                result: HashSet::new(),
            };
            for p in destination
                .as_ref()
                .into_iter()
                .map(|p| p.0)
                .chain(args.iter().filter_map(mir::Operand::place))
            {
                <RegionCollector as ty::fold::TypeVisitor>::visit_ty(
                    &mut collector,
                    p.ty(self.body, self.tcx).ty,
                );
            }
            for vid in collector.result {
                self.handle_vid(vid);
                let tidx = self.terminator_index;
                self.result.insert((tidx, vid));
            }
            self.terminator_index += 1;
        }
        self.super_terminator(terminator, location)
    }

    fn visit_statement(&mut self, statement: &mir::Statement<'tcx>, location: Location) {
        debug!("Visiting statement {:?}", statement.kind);
        self.super_statement(statement, location)
    }

    fn visit_place(
        &mut self,
        place: &Place<'tcx>,
        context: mir::visit::PlaceContext,
        location: Location,
    ) {
        let mut collector = RegionCollector {
            result: HashSet::new(),
        };
        <RegionCollector as ty::fold::TypeVisitor>::visit_ty(
            &mut collector,
            place.ty(self.body, self.tcx).ty,
        );
        let set = collector.result;
        if !set.is_empty() {
            debug!("{place:?} at location {location:?} contains regions {set:?}");
        }
        self.super_place(place, context, location)
    }

    fn visit_region(&mut self, region: ty::Region<'tcx>, _: Location) {
        debug!("Saw region {:?}", region);
        if let RegionKind::ReVar(v) = region.kind() {
            self.handle_vid(v);
        }
        self.super_region(region)
    }
}

extern crate polonius_engine;

type LocationIndex = <rustc_borrowck::consumers::RustcFacts as polonius_engine::FactTypes>::Point;

enum ConstraintSelector<'tcx, 'a> {
    LocationBased {
        body_with_facts: &'a BodyWithBorrowckFacts<'tcx>,
    },
    EntailmentMatchingBased {
        elimination_set: HashSet<(RegionVid, RegionVid)>,
    },
}

impl<'a, 'tcx> ConstraintSelector<'tcx, 'a> {
    fn location_based(body_with_facts: &'a BodyWithBorrowckFacts<'tcx>) -> Self {
        Self::LocationBased { body_with_facts }
    }
    fn entailment_matching_based(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Self {
        let mut vis = ComputeCallObligations::new(tcx, body);
        <ComputeCallObligations as mir::visit::Visitor>::visit_body(&mut vis, body);
        debug!(
            "Largest vid seen: {:?}, highest terminator index: {}",
            vis.largest_vid, vis.terminator_index
        );
        let elimination_set = vis.result();
        debug!("Found region obligations {:?}", elimination_set);
        Self::EntailmentMatchingBased { elimination_set }
    }
    fn select(&self, r1: RegionVid, r2: RegionVid, idx: LocationIndex) -> bool {
        let allow = match self {
            Self::LocationBased { body_with_facts } => {
                use rustc_borrowck::consumers::RichLocation;
                let rich_loc = body_with_facts.location_table.to_location(idx);
                let loc = match rich_loc {
                    RichLocation::Mid(l) => l,
                    RichLocation::Start(l) => l,
                };
                let stmt = body_with_facts.body.stmt_at(loc);
                match &stmt {
                    Either::Right(term) => {
                        debug!("Introduced by {:?} @ {rich_loc:?} ({idx:?})", term.kind)
                    }
                    Either::Left(stmt) => debug!("Introduced by {:?} @ {rich_loc:?}", stmt.kind),
                };
                !matches!(
                    stmt,
                    Either::Right(Terminator {
                        kind: TerminatorKind::Call { .. },
                        ..
                    })
                )
            }
            Self::EntailmentMatchingBased { elimination_set } => {
                !elimination_set.contains(&(r1, r2))
            }
        };
        debug!(
            "{} entailment {:?} -> {:?}",
            if allow { "Allowing" } else { "Eliminating" },
            r1,
            r2
        );
        allow
    }
}

/// Perform a depth-first search up the dependency tree formed from looking up
/// the [`places_read`] at a location in `g`, starting from `loc`.
///
/// Terminates on each branch when a location `l` is encountered that does not
/// satisfy `matches!(Keep::from_global_location(tcx, l), Keep::Reject(_))`.
///
/// In addition the set of places that is considered "read" for `loc` (the
/// initial location) is
/// [`Aliases::reachable_values(p)`](flowistry::mir::aliases::Aliases::reachable_values).
/// This means we consider all subplaces as also read. This only makes sense for
/// function calls, hence this should only be called on locations that represent
/// function calls.
pub fn deep_dependencies_of<'tcx, 'g>(
    tcx: TyCtxt<'tcx>,
    aliases: &flowistry::mir::aliases::Aliases<'_, 'tcx>,
    loc: GlobalLocation<'g>,
    g: &GlobalFlowGraph<'tcx, 'g>,
    p: mir::Place<'tcx>,
    use_reachable_places: Option<(mir::Mutability, bool)>,
) -> HashSet<GlobalLocation<'g>> {
    let (inner_loc, inner_body) = loc.innermost_location_and_body();
    let def_id = tcx.hir().body_owner_def_id(inner_body);
    let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, def_id);
    let stmt = body_with_facts.simplified_body().stmt_at(inner_loc);
    if !matches!(
        stmt,
        Either::Right(Terminator {
            kind: TerminatorKind::Call { .. },
            ..
        })
    ) {
        warn!("`deep_dependencies_of` was called on non-function-call location {} with statement {:?}", loc, stmt);
    }
    // Get the combined dependencies for `places` at the
    // location `loc` also taking into account provenance.
    let deps_for_places = |loc: GlobalLocation<'g>, places: &[Place<'tcx>]| {
        places
            .iter()
            .filter_map(|place| {
                provenance_of(tcx, *place)
                    .into_iter()
                    .find_map(|place| Some((place, g.location_states.get(&loc)?.resolve(place))))
            })
            .flat_map(|(p, (new_place, s))| s.map(move |l| (new_place.unwrap_or(p), l)))
            .collect::<Vec<(Place<'tcx>, GlobalLocation<'g>)>>()
    };

    // See https://www.notion.so/justus-adam/Call-chain-analysis-26fb36e29f7e4750a270c8d237a527c1#b5dfc64d531749de904a9fb85522949c
    let reachable_places = if let Some((m, use_locations)) = use_reachable_places {
        let selector = if use_locations {
            ConstraintSelector::location_based(body_with_facts.body_with_facts())
        } else {
            ConstraintSelector::entailment_matching_based(tcx, &body_with_facts.simplified_body())
        };
        let new_aliases = flowistry::mir::aliases::Aliases::build_with_fact_selection(
            tcx,
            def_id.to_def_id(),
            body_with_facts,
            |r1, r2, idx| selector.select(r1, r2, idx),
        );
        let a = new_aliases
            .reachable_values(p, m)
            .into_iter()
            .flat_map(|&p| new_aliases.conflicts(p).iter())
            .cloned()
            .filter(|p| p.is_direct(body_with_facts.borrowckd_body()))
            .collect::<Vec<_>>();

        debug!("Determined the reachable places ({m:?}) for {p:?} @ {loc} are {a:?}");
        debug!("Aliases would have been {:?}", new_aliases.aliases(p));
        a
    } else {
        vec![p]
    };
    let mut queue = deps_for_places(loc, &reachable_places);
    let mut seen = HashSet::new();
    let mut deps = HashSet::new();

    // A reverse dfs traversing the flowistry tensor which terminates every time we find a function call.
    while let Some((place, location)) = queue.pop() {
        // A special situation has ocurred. We've hit a translation boundary
        // (either an argument or a call site of an inlined function). This
        // causes a translation of the place, but otherwise this location must
        // be rejected so we translate, resolve and move on.
        if g.location_states.get(&location).map(|s| s.is_translated()) == Some(true) {
            // Don't insert this location into `seen`, because we might cross
            // this boundary multiple times with different places
            queue.extend(deps_for_places(location, &[place]));
        } else {
            match Keep::from_global_location(tcx, location) {
                Keep::Keep(..) | Keep::Argument(_) => {
                    debug!(
                        "Found dependency from {p:?} on {location} via the last place {place:?}"
                    );
                    deps.insert(location);
                }
                Keep::Reject(stmt_at_loc) if !seen.contains(&location) => {
                    seen.insert(location);
                    if let Some(stmt) = stmt_at_loc {
                        queue.extend(deps_for_places(
                            location,
                            &places_read(tcx, location.innermost_location_and_body().0, &stmt)
                                .collect::<Vec<_>>(),
                        ));
                    } else {
                        error!("Rejection without statement should not happen anymore. Rejected {location} without statement");
                    }
                }
                _ => (),
            }
        }
    }
    deps
}

/// A struct responsible for creating a global flow matrix for one `mir::Body`,
/// inlining all callees (that are configured to be inlined). It is a similar
/// idea to `GlobalFlowConstructor` (in fact it wraps one) that bundles together
/// all information needed to inline into one `mir::Body` so that we can split
/// it into helper functions which all have access to this information.
///
/// ## Usage
///
/// The function inliner implements `mir::visit::Visitor` that should be applied
/// to only the same `Body` this struct was initialized with.
///
/// The methods are currently split into the visit methods that actually modify
/// `self.under_construction` and helper methods such as
/// `self.handle_regular_location` that take an immutable `&self` and return
/// their computed results instead of appending them directly to
/// `under_construction`. This is so that we can use these functions
/// agnostically and later make a determination about where to insert their
/// results. For instance the result of `handle_regular_location` is both
/// inserted into `location_states` but also added to `return_state` when we are
/// handling a terminator. However `handle_regular_location` itself does not
/// know in which context it is being used (to make its implementation simpler).
pub struct FunctionInliner<'tcx, 'g, 'opts, 'refs, I: InlineSelector + Clone> {
    // Read-only information
    /// The parent constructor struct. For the function we will be inlining we
    /// operate on the flows that this parent has already computed.
    flow_constructor: &'refs GlobalFlowConstructor<'tcx, 'g, 'opts, I>,
    /// A flowistry analysis of `body`
    from_flowistry:
        &'refs AnalysisResults<'tcx, FlowAnalysis<'tcx, 'tcx, NonTransitiveFlowDomain<'tcx>>>,
    /// The source MIR for the body into which we are inlining
    body: &'tcx mir::Body<'tcx>,
    /// The local def id of `body`
    local_def_id: LocalDefId,
    /// The body id of `body`
    root_function: BodyId,

    /// The graph we are currently constructing.
    under_construction: GlobalFlowGraph<'tcx, 'g>,
}

impl<'tcx, 'g, 'opts, 'refs, I: InlineSelector + Clone> FunctionInliner<'tcx, 'g, 'opts, 'refs, I> {
    /// Convenient access to the `TyCtxt`
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.flow_constructor.tcx
    }
    /// Convenient access to the `GLI`
    fn gli(&self) -> GLI<'g> {
        self.flow_constructor.gli
    }

    /// Transform the dependency row for `loc` into one with global locations.
    ///
    /// This is what is done for locations that are non-inlineable calls.
    fn handle_regular_location(&self, loc: mir::Location) -> GlobalDepMatrix<'tcx, 'g> {
        let matrix = self.from_flowistry.state_at(loc).matrix();
        if self.flow_constructor.dbg_opts.dump_flowistry_matrix {
            debug!(
                "Flowistry matrix at {loc:?}\n{}",
                dbg::PrintableMatrix(matrix)
            );
        }
        matrix
            .rows()
            .map(|(place, dep_set)| (place, self.make_row_global(dep_set)))
            .collect::<HashMap<_, _>>()
    }

    /// Makes `callee` relative to `call_site` in the function we operate on,
    /// i.e. `self.root_function`
    ///
    /// This returns a closure so that we can detach from `self`. This is
    /// possible because this function only needs read only/copy data. This
    /// allows you to do something like
    ///
    /// ```
    /// let make_relative_location = self.relative_location_maker();
    /// let it = some_vec
    ///     .iter()
    ///     .map(|elem| make_relative_location(..., elem));
    /// self.under_construction.extend(it);
    /// ```
    ///
    /// E.g. you can borrow the closure in an iterator and still mutably modify
    /// `self`.
    fn relative_global_location_maker(
        &self,
    ) -> impl Fn(mir::Location, GlobalLocation<'g>) -> GlobalLocation<'g> {
        let gli = self.gli();
        let root_function = self.root_function;
        move |call_site, callee| gli.global_location_from_relative(callee, call_site, root_function)
    }

    /// Create a [`PlaceTranslationTable`] that maps places from the callee
    /// (`inner_flow`) to the caller (`self.body`).
    fn create_callee_to_caller_translation_table(
        &self,
        inner_flow: &FunctionFlow<'tcx, 'g>,
        args: &[Option<mir::Place<'tcx>>],
        inner_body: &mir::Body<'tcx>,
        dest: Option<(mir::Place<'tcx>, mir::BasicBlock)>,
    ) -> PlaceTranslationTable<'tcx> {
        inner_flow
            .flow
            .location_states
            .values()
            .flat_map(|s| s.keys())
            .collect::<HashSet<_>>()
            .into_iter()
            .filter_map(|child| {
                Some((
                    child,
                    translate_child_to_parent(
                        self.tcx(),
                        self.local_def_id,
                        args,
                        dest,
                        child,
                        false,
                        inner_body,
                        self.body,
                    )?,
                ))
            })
            .collect::<HashMap<_, _>>()
    }

    /// Create a [`PlaceTranslationTable`] that maps places from the caller
    /// (`self.body`) to places in the callee (`inner_flow`).
    fn create_caller_to_callee_translation_table(
        &self,
        args: &[Option<mir::Place<'tcx>>],
        destination: Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        inner_body: &mir::Body<'tcx>,
        inner_flow: &FunctionFlow<'tcx, 'g>,
    ) -> PlaceTranslationTable<'tcx> {
        inner_flow
            .flow
            .return_state
            .keys()
            .flat_map(|&child| {
                let parent = translate_child_to_parent(
                    self.tcx(),
                    self.local_def_id,
                    &args,
                    destination,
                    child,
                    true,
                    inner_body,
                    self.body,
                );
                let alias_info = &self.from_flowistry.analysis.aliases;
                let aliases = parent
                    .into_iter()
                    .flat_map(|p| alias_info.aliases(p).iter())
                    .collect::<Vec<_>>();
                aliases.into_iter().map(move |&parent| (parent, child))
            })
            .collect::<HashMap<_, _>>()
    }

    /// Transform the dependencies ([`Location`]s as calculated by flowistry)
    /// into global locations.
    ///
    /// Either simply calls [`GLI::globalize_location`] or, for [`Location`]s
    /// that name calls to functions which are to be inlined, query the return
    /// state of that call, translate `place` to a place in that return state
    /// and merge in the dependencies for the translated place.
    fn make_row_global(
        &self,
        dep_set: IndexSet<mir::Location, flowistry::indexed::RefSet<mir::Location>>,
    ) -> HashSet<GlobalLocation<'g>> {
        dep_set
            .iter()
            .map(|l| self.gli().globalize_location(*l, self.root_function))
            .collect()
    }
}

impl<'tcx, 'g, 'opts, 'refs, I: InlineSelector + Clone> mir::visit::Visitor<'tcx>
    for FunctionInliner<'tcx, 'g, 'opts, 'refs, I>
{
    fn visit_statement(&mut self, _statement: &mir::Statement<'tcx>, location: Location) {
        let regular_result = self.handle_regular_location(location);
        let global_loc = self.gli().globalize_location(location, self.root_function);
        self.under_construction
            //.borrow_mut()
            .location_states
            .insert(
                global_loc,
                TranslatedDepMatrix::untranslated(regular_result),
            );
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        // First we handle this as the default case. This
        // also recurses as necessary
        let state_at_term = self.handle_regular_location(location);
        if let Ok((inner_flow, inner_body_id, inner_body, args, dest)) =
            self.flow_constructor.inner_flow_for_terminator(terminator)
        {
            // A translation table from places in `inner_flow` to places from
            // `self.body` by lining them up at the arguments.
            //
            // Constructed by optimistically translating every place in the
            // callee to a place in the caller. This allows us to uphold the
            // invariant that when tracing dependencies a local place does not
            // immediately cross into a parent, but first into such an argument
            // location where it can get translated.
            let parent_translation_matrix = self.create_callee_to_caller_translation_table(
                &inner_flow,
                args.as_slice(),
                inner_body,
                dest,
            );
            // A special dependency matrix that will be inserted at the argument
            // locations which performs translation from callee places to caller
            // places.
            let parent_dep_matrix =
                TranslatedDepMatrix::translated(state_at_term, parent_translation_matrix);
            debug!(
                "Calculated parent dependency matrix at terminator {:?}\n{}",
                terminator.kind,
                dbg::PrintableDependencyMatrix::new(parent_dep_matrix.matrix_raw(), 2)
            );

            let gli = self.gli();
            let root_function = self.root_function;
            // Construct this closure detached form `self` here so we can
            // reference it in the upcoming iterators while still mutably
            // modifying `self.under_construction`
            let make_relative_location = self.relative_global_location_maker();
            let local_relativizer = |dep| make_relative_location(location, dep);

            // Now we build up all the locations we will splice into our graph.

            // First we make a new, relative location for every regular (i.e.
            // not an argument) location in the inner graph
            let translated_inner_locations =
                inner_flow
                    .flow
                    .location_states
                    .iter()
                    .map(|(inner_loc, map)| {
                        (
                            make_relative_location(location, *inner_loc),
                            map.relativize(local_relativizer),
                        )
                    });

            // The we add the argument locations. These are special, because the
            // also perform place translation (see `TranslatedDepMatrix`)
            let argument_locations = (1..=args.len()).into_iter().map(|a| {
                let global_call_site = gli.globalize_location(
                    mir::Location {
                        block: mir::BasicBlock::from_usize(inner_body.basic_blocks().len()),
                        statement_index: a,
                    },
                    inner_body_id,
                );
                let global_arg_loc = make_relative_location(location, global_call_site);
                (global_arg_loc, parent_dep_matrix.clone())
            });

            // Lastly we create a location for this call site. This is also a
            // special, translating location and represents the return state
            // from calling `inner_flow` at this call site (see `TranslatedDepMatrix`).
            let call_site_location = (
                gli.globalize_location(location, root_function),
                TranslatedDepMatrix::translated(
                    relativize_global_dep_matrix(&inner_flow.flow.return_state, local_relativizer),
                    self.create_caller_to_callee_translation_table(
                        args.as_slice(),
                        dest,
                        inner_body,
                        inner_flow.borrow(),
                    ),
                ),
            );

            // Add all of them into our flow.
            self.under_construction.location_states.extend(
                translated_inner_locations
                    .chain(argument_locations)
                    .chain(std::iter::once(call_site_location)),
            );
        } else {
            // In the special case of a `return` terminator we
            // merge its state onto any prior state for the
            // return
            if let TerminatorKind::Return = terminator.kind {
                for (p, deps) in state_at_term.iter() {
                    self.under_construction
                        .return_state
                        .entry(*p)
                        .or_insert_with(|| HashSet::new())
                        .extend(deps.iter().cloned());
                }
            };
            self.under_construction.location_states.insert(
                self.gli().globalize_location(location, self.root_function),
                TranslatedDepMatrix::untranslated(state_at_term),
            );
        }
    }
}

/// A helper struct classifying whether a given `GlobalLocation` should be kept
/// during `compute_call_only_flow`. The main way to use this struct is with the
/// `from_location` function which also has additional documentation.
enum Keep<'tcx> {
    Keep(
        SimplifiedArguments<'tcx>,
        Option<(Place<'tcx>, mir::BasicBlock)>,
    ),
    Argument(usize),
    Reject(Option<Either<&'tcx mir::Statement<'tcx>, &'tcx mir::Terminator<'tcx>>>),
}

impl<'tcx> Keep<'tcx> {
    /// Same as [`from_location`](Self::from_location) but operating on
    /// [`GlobalLocation`]s.
    ///
    /// Global locations are easily used wrong in subtle ways (see also [its
    /// documentation](crate::ir::global_location)) and this method ensures the correct
    /// information from the global locations are used to construct a [`Keep`]
    /// value (i.e. the innermost location is queried).
    fn from_global_location(tcx: TyCtxt<'tcx>, location: GlobalLocation) -> Self {
        let (local_inner_loc, local_inner_body) = location.innermost_location_and_body();
        Self::from_location(
            tcx,
            local_inner_body,
            local_inner_loc,
            location.is_at_root(),
        )
    }
    /// This is an important function that is used multiple times throughout the
    /// dfs later. It is a selector for which locations to keep in the reduced
    /// graph but in addition its variants also transport necessary
    /// information for the search algorithm. This design was chosen because it
    /// allows the use of the same function when we try to figure out whether to
    /// use the location as a sink or a source and also transport some data we
    /// inevitably calculate during that determination.
    fn from_location(
        tcx: TyCtxt<'tcx>,
        body_id: BodyId,
        location: Location,
        loc_is_top_level: bool,
    ) -> Self {
        let body_with_facts =
            borrowck_facts::get_body_with_borrowck_facts(tcx, tcx.hir().body_owner_def_id(body_id));
        if !is_real_location(&body_with_facts.simplified_body(), location) {
            if loc_is_top_level {
                Keep::Argument(location.statement_index)
            } else {
                Keep::Reject(None)
            }
        } else {
            let stmt_at_loc = body_with_facts.simplified_body().stmt_at(location);
            match stmt_at_loc {
                Either::Right(t) => t
                    .as_fn_and_args()
                    .ok()
                    .map_or(Keep::Reject(Some(stmt_at_loc)), |(_, args, dest)| {
                        Keep::Keep(args, dest)
                    }),
                _ => Keep::Reject(Some(stmt_at_loc)),
            }
        }
    }

    /// If this is a `Keep::Keep` variant return its payload, otherwise noting.
    fn into_keep(
        self,
    ) -> Option<(
        SimplifiedArguments<'tcx>,
        Option<(Place<'tcx>, mir::BasicBlock)>,
    )> {
        match self {
            Keep::Keep(args, dest) => Some((args, dest)),
            _ => None,
        }
    }
}

impl<'tcx, 'g> Flow<'tcx, 'g> {
    /// Canonical way to construct a [`Flow`].
    ///
    /// Takes care of constructing in accordance with the configuration in
    /// `opts`.
    fn compute<P: InlineSelector + Clone + 'static>(
        opts: &crate::AnalysisCtrl,
        dbg_opts: &crate::DbgArgs,
        tcx: TyCtxt<'tcx>,
        body_id: BodyId,
        gli: GLI<'g>,
        inline_selector: P,
    ) -> Self {
        let mut eval_mode = flowistry::extensions::EvalMode::default();
        if !opts.no_recursive_analysis {
            eval_mode.context_mode = flowistry::extensions::ContextMode::Recurse;
        }
        let constructor = GlobalFlowConstructor::new(opts, dbg_opts, tcx, gli, inline_selector);
        let granular_flow = constructor.compute_granular_global_flows(body_id).unwrap();
        debug!(
            "Granular flow for {}\n{:?}",
            body_name_pls(tcx, body_id).name,
            dbg::PrintableGranularFlow {
                flow: &granular_flow.flow,
                tcx
            }
        );
        if dbg_opts.dump_inlined_function_flow {
            outfile_pls(format!("{}.inlined-flow.gv", body_name_pls(tcx, body_id)))
                .and_then(|mut f| dbg::call_only_flow_dot::dump(tcx, &granular_flow.flow, &mut f))
                .unwrap();
        }

        let reduced_flow = constructor.compute_call_only_flow(&granular_flow.flow);
        debug!(
            "Constructed reduced flow of {} locations\n{:?}",
            reduced_flow.len(),
            reduced_flow.keys()
        );
        Self {
            root_function: body_id,
            function_flows: constructor.function_flows,
            reduced_flow,
        }
    }
}

/// The only implementation of [`InlineSelector`] currently in use. This skips
/// inlining for all `LocalDefId` values that are found in the map of
/// `self.marked_objects` i.e. all those functions that have annotations.
#[derive(Clone)]
struct SkipAnnotatedFunctionSelector {
    marked_objects: MarkedObjects,
}

impl InlineSelector for SkipAnnotatedFunctionSelector {
    fn should_inline(&self, tcx: TyCtxt, did: LocalDefId) -> bool {
        self.marked_objects
            .as_ref()
            .borrow()
            .get(&tcx.hir().local_def_id_to_hir_id(did))
            .map_or(true, |anns| anns.0.is_empty())
    }
}

/// A map of objects for which we have found annotations.
///
/// This is sharable so we can stick it into the
/// [`SkipAnnotatedFunctionSelector`]. Technically at that point this map is
/// read-only.
type MarkedObjects = Rc<RefCell<HashMap<HirId, (Vec<Annotation>, ObjectType)>>>;

/// This visitor traverses the items in the analyzed crate to discover
/// annotations and analysis targets and store them in this struct. After the
/// discovery phase [`Self::analyze`] is used to drive the
/// actual analysis. All of this is conveniently encapsulated in the
/// [`Self::run`] method.
pub struct CollectingVisitor<'tcx> {
    /// Reference to rust compiler queries.
    tcx: TyCtxt<'tcx>,
    /// Command line arguments.
    opts: &'static crate::Args,
    /// In this map we will be accumulating the definitions we found annotations
    /// for (except `analyze` annotations, those are in `function_to_analyze`),
    /// which annotations they are and what type of item it is.
    marked_objects: MarkedObjects,
    /// Expressions and statements we found annotations on. At the moment those
    /// should only be [`ExceptionAnnotation`]s.
    marked_stmts: HashMap<HirId, ((Vec<Annotation>, usize), Span, DefId)>,
    /// Functions that are annotated with `#[dfpp::analyze]`. For these we will
    /// later perform the analysis
    functions_to_analyze: Vec<(Ident, BodyId, &'tcx rustc_hir::FnDecl<'tcx>)>,
}

impl<'tcx> CollectingVisitor<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, opts: &'static crate::Args) -> Self {
        Self {
            tcx,
            opts,
            marked_objects: Rc::new(RefCell::new(HashMap::new())),
            marked_stmts: HashMap::new(),
            functions_to_analyze: vec![],
        }
    }

    /// Does the function named by this id have the `dfpp::analyze` annotation
    fn should_analyze_function(&self, ident: HirId) -> bool {
        self.tcx
            .hir()
            .attrs(ident)
            .iter()
            .any(|a| a.matches_path(&consts::ANALYZE_MARKER))
    }

    /// Driver function. Performs the data collection via visit, then calls
    /// [`Self::analyze`] to construct the Forge friendly description of all
    /// endpoints.
    pub fn run(mut self) -> std::io::Result<ProgramDescription> {
        let tcx = self.tcx;
        tcx.hir().deep_visit_all_item_likes(&mut self);
        //println!("{:?}\n{:?}\n{:?}", self.marked_sinks, self.marked_sources, self.functions_to_analyze);
        self.analyze()
    }

    /// Extract all types mentioned in this type for which we have annotations.
    fn annotated_subtypes(&self, ty: ty::Ty) -> HashSet<TypeDescriptor> {
        ty.walk()
            .filter_map(|ty| {
                generic_arg_as_type(ty)
                    .and_then(ty_def)
                    .and_then(DefId::as_local)
                    .and_then(|def| {
                        let hid = self.tcx.hir().local_def_id_to_hir_id(def);
                        if self.marked_objects.as_ref().borrow().contains_key(&hid) {
                            Some(Identifier::new(
                                self.tcx
                                    .item_name(self.tcx.hir().local_def_id(hid).to_def_id()),
                            ))
                        } else {
                            None
                        }
                    })
            })
            .collect()
    }

    /// Perform the analysis for one `#[dfpp::analyze]` annotated function and
    /// return the representation suitable for emitting into Forge.
    fn handle_target<'g>(
        &self,
        _hash_verifications: &mut HashVerifications,
        call_site_annotations: &mut CallSiteAnnotations,
        interesting_fn_defs: &HashMap<DefId, (Vec<Annotation>, usize)>,
        id: Ident,
        b: BodyId,
        gli: GLI<'g>,
    ) -> std::io::Result<(Endpoint, Ctrl)> {
        let mut flows = Ctrl::new();
        let local_def_id = self.tcx.hir().body_owner_def_id(b);
        fn register_call_site<'tcx>(
            tcx: TyCtxt<'tcx>,
            map: &mut CallSiteAnnotations,
            did: DefId,
            ann: Option<&[Annotation]>,
        ) {
            map.entry(did)
                .and_modify(|e| {
                    e.0.extend(ann.iter().flat_map(|a| a.iter()).cloned());
                })
                .or_insert_with(|| {
                    (
                        ann.iter().flat_map(|a| a.iter()).cloned().collect(),
                        tcx.fn_sig(did).skip_binder().inputs().len(),
                    )
                });
        }
        let tcx = self.tcx;
        let controller_body_with_facts =
            borrowck_facts::get_body_with_borrowck_facts(tcx, local_def_id);

        if self.opts.dbg.dump_ctrl_mir {
            mir::graphviz::write_mir_fn_graphviz(
                tcx,
                &controller_body_with_facts.simplified_body(),
                false,
                &mut outfile_pls(format!("{}.mir.gv", id.name)).unwrap(),
            )
            .unwrap()
        }

        debug!("Handling target {}", id.name);
        let flow = Flow::compute(
            &self.opts.anactrl,
            &self.opts.dbg,
            tcx,
            b,
            gli,
            SkipAnnotatedFunctionSelector {
                marked_objects: self.marked_objects.clone(),
            },
        );

        // Register annotations on argument types for this controller.
        let controller_body = &controller_body_with_facts.simplified_body();
        {
            let types = controller_body.args_iter().map(|l| {
                let ty = controller_body.local_decls[l].ty;
                let subtypes = self.annotated_subtypes(ty);
                (DataSource::Argument(l.as_usize() - 1), subtypes)
            });
            flows.add_types(types);
        }

        if self.opts.dbg.dump_serialized_non_transitive_graph {
            dbg::write_non_transitive_graph_and_body(
                tcx,
                &flow.reduced_flow,
                outfile_pls(format!("{}.ntgb.json", id.name)).unwrap(),
            );
        }

        if self.opts.dbg.dump_non_transitive_graph {
            outfile_pls(format!("{}.call-only-flow.gv", id.name))
                .and_then(|mut file| {
                    dbg::call_only_flow_dot::dump(tcx, &flow.reduced_flow, &mut file)
                })
                .unwrap_or_else(|err| {
                    error!("Could not write transitive graph dump, reason: {err}")
                })
        }

        for (loc, deps) in flow.reduced_flow.iter() {
            // It's important to look at the innermost location. It's easy to
            // use `location()` and `function()` on a global location instead
            // but that is the outermost call site, not the location for the actual call.
            let (inner_location, inner_body_id) = loc.innermost_location_and_body();
            // We need to make sure to fetch the body again here, because we
            // might be looking at an inlined location, so the body we operate
            // on bight not be the `body` we fetched before.
            let inner_body_with_facts = tcx.body_for_body_id(inner_body_id);
            let ref inner_body = inner_body_with_facts.simplified_body();
            if !is_real_location(&inner_body, inner_location) {
                assert!(loc.is_at_root());
                // These can only be (controller) arguments and they cannot have
                // dependencies (and thus not receive any data)
                continue;
            }
            let (terminator, (defid, _, _)) = match inner_body
                .stmt_at(inner_location)
                .right()
                .ok_or("not a terminator")
                .and_then(|t| Ok((t, t.as_fn_and_args()?)))
            {
                Ok(term) => term,
                Err(err) => {
                    // We expect to always encounter function calls at this
                    // stage so this could be a hard error, but I made it a
                    // warning because that makes it easier to debug (because
                    // you can see other important down-the-line output that
                    // gives moire information to this error).
                    warn!(
                        "Odd location in graph creation '{}' for {:?}",
                        err,
                        inner_body.stmt_at(inner_location)
                    );
                    continue;
                }
            };
            let call_site = CallSite {
                called_from: Identifier::new(body_name_pls(tcx, inner_body_id).name),
                location: inner_location,
                function: identifier_for_fn(tcx, defid),
            };
            // Propagate annotations on the function object to the call site
            register_call_site(
                tcx,
                call_site_annotations,
                defid,
                interesting_fn_defs.get(&defid).map(|a| a.0.as_slice()),
            );

            let stmt_anns = self.statement_anns_by_loc(defid, terminator);
            let bound_sig = tcx.fn_sig(defid);
            let interesting_output_types: HashSet<_> =
                self.annotated_subtypes(bound_sig.skip_binder().output());
            if !interesting_output_types.is_empty() {
                flows.types.0.insert(
                    DataSource::FunctionCall(call_site.clone()),
                    interesting_output_types,
                );
            }
            if let Some(_anns) = stmt_anns {
                // This is currently commented out because hash verification is
                // buggy
                unimplemented!();
                // for ann in anns.iter().filter_map(Annotation::as_exception_annotation) {
                //     //hash_verifications.handle(ann, tcx, terminator, &body, loc, matrix);
                // }
                // TODO this is attaching to functions instead of call
                // sites. Once we start actually tracking call sites
                // this needs to be adjusted
                // register_call_site(tcx, call_site_annotations, defid, Some(anns));
            }

            for (arg_slot, arg_deps) in deps.input_deps.iter().enumerate() {
                // This will be the target of any flow we register
                let to = if loc.is_at_root()
                    && matches!(
                        inner_body.stmt_at(loc.location()),
                        Either::Right(mir::Terminator {
                            kind: mir::TerminatorKind::Return,
                            ..
                        })
                    ) {
                    DataSink::Return
                } else {
                    DataSink::Argument {
                        function: call_site.clone(),
                        arg_slot,
                    }
                };
                for dep in arg_deps.iter() {
                    flows.add(
                        Cow::Owned(dep.as_data_source(tcx, |l| is_real_location(&inner_body, l))),
                        to.clone(),
                    );
                }
            }
        }
        Ok((Identifier::new(id.name), flows))
    }

    /// Main analysis driver. Essentially just calls [`Self::handle_target`]
    /// once for every function in `self.functions_to_analyze` after doing some
    /// other setup necessary for the flow graph creation.
    ///
    /// Should only be called after the visit.
    fn analyze(mut self) -> std::io::Result<ProgramDescription> {
        let arena = rustc_arena::TypedArena::default();
        let interner = GlobalLocationInterner::new(&arena);
        let gli = GLI::new(&interner);
        let tcx = self.tcx;
        let mut targets = std::mem::replace(&mut self.functions_to_analyze, vec![]);
        let interesting_fn_defs = self
            .marked_objects
            .as_ref()
            .borrow()
            .iter()
            .filter_map(|(s, v)| match v.1 {
                ObjectType::Function(i) => {
                    Some((tcx.hir().local_def_id(*s).to_def_id(), (v.0.clone(), i)))
                }
                _ => None,
            })
            .collect::<HashMap<_, _>>();
        let mut call_site_annotations: CallSiteAnnotations = HashMap::new();
        crate::sah::HashVerifications::with(|hash_verifications| {
            targets
                .drain(..)
                .map(|(id, b, _)| {
                    self.handle_target(
                        hash_verifications,
                        &mut call_site_annotations,
                        &interesting_fn_defs,
                        id,
                        b,
                        gli,
                    )
                })
                .collect::<std::io::Result<HashMap<Endpoint, Ctrl>>>()
                .map(|controllers| ProgramDescription {
                    controllers,
                    annotations: call_site_annotations
                        .into_iter()
                        .map(|(k, v)| (identifier_for_fn(tcx, k), (v.0, ObjectType::Function(v.1))))
                        .chain(
                            self.marked_objects
                                .as_ref()
                                .borrow()
                                .iter()
                                .filter(|kv| kv.1 .1 == ObjectType::Type)
                                .map(|(k, v)| (identifier_for_hid(tcx, *k), v.clone())),
                        )
                        .collect(),
                })
        })
    }

    /// XXX: This selector is somewhat problematic. For one it matches via
    /// source locations, rather than id, and for another we're using `find`
    /// here, which would discard additional matching annotations.
    fn statement_anns_by_loc(&self, p: DefId, t: &mir::Terminator<'tcx>) -> Option<&[Annotation]> {
        self.marked_stmts
            .iter()
            .find(|(_, (_, s, f))| p == *f && s.contains(t.source_info.span))
            .map(|t| t.1 .0 .0.as_slice())
    }
}

/// Confusingly named this function actually computed the highest index
/// mentioned in any `on_argument` refinement in the provided annotation slice.
fn obj_type_for_stmt_ann(anns: &[Annotation]) -> usize {
    *anns
        .iter()
        .flat_map(|a| match a {
            Annotation::Label(LabelAnnotation { refinement, .. }) => {
                Box::new(refinement.on_argument().iter()) as Box<dyn Iterator<Item = &u16>>
            }
            Annotation::Exception(_) => Box::new(std::iter::once(&0)),
            _ => panic!("Unsupported annotation type for statement annotation"),
        })
        .max()
        .unwrap() as usize
}

impl<'tcx> intravisit::Visitor<'tcx> for CollectingVisitor<'tcx> {
    type NestedFilter = OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    /// Checks for annotations on this id and collects all those id's that have
    /// been annotated.
    fn visit_id(&mut self, id: HirId) {
        let tcx = self.tcx;
        let hir = self.tcx.hir();
        let sink_matches = hir
            .attrs(id)
            .iter()
            .filter_map(|a| {
                a.match_extract(&consts::LABEL_MARKER, |i| {
                    Annotation::Label(crate::ann_parse::ann_match_fn(i))
                })
                .or_else(|| {
                    a.match_extract(&consts::OTYPE_MARKER, |i| {
                        Annotation::OType(crate::ann_parse::otype_ann_match(i))
                    })
                })
                .or_else(|| {
                    a.match_extract(&consts::EXCEPTION_MARKER, |i| {
                        Annotation::Exception(crate::ann_parse::match_exception(i))
                    })
                })
            })
            .collect::<Vec<_>>();
        if !sink_matches.is_empty() {
            let node = self.tcx.hir().find(id).unwrap();
            assert!(if let Some(decl) = node.fn_decl() {
                self.marked_objects
                    .as_ref()
                    .borrow_mut()
                    .insert(id, (sink_matches, ObjectType::Function(decl.inputs.len())))
                    .is_none()
            } else {
                match node {
                    hir::Node::Ty(_)
                    | hir::Node::Item(hir::Item {
                        kind: hir::ItemKind::Struct(..),
                        ..
                    }) => self
                        .marked_objects
                        .as_ref()
                        .borrow_mut()
                        .insert(id, (sink_matches, ObjectType::Type))
                        .is_none(),
                    _ => {
                        let e = match node {
                            hir::Node::Expr(e) => e,
                            hir::Node::Stmt(hir::Stmt { kind, .. }) => match kind {
                                hir::StmtKind::Expr(e) | hir::StmtKind::Semi(e) => e,
                                _ => panic!("Unsupported statement kind"),
                            },
                            _ => panic!("Unsupported object type for annotation {node:?}"),
                        };
                        let obj_type = obj_type_for_stmt_ann(&sink_matches);
                        let did = match e.kind {
                            hir::ExprKind::MethodCall(_, _, _) => {
                                let body_id = hir.enclosing_body_owner(id);
                                let tcres = tcx.typeck(hir.local_def_id(body_id));
                                tcres.type_dependent_def_id(e.hir_id).unwrap_or_else(|| {
                                    panic!("No DefId found for method call {e:?}")
                                })
                            }
                            hir::ExprKind::Call(
                                hir::Expr {
                                    hir_id,
                                    kind: hir::ExprKind::Path(p),
                                    ..
                                },
                                _,
                            ) => {
                                let body_id = hir.enclosing_body_owner(id);
                                let tcres = tcx.typeck(hir.local_def_id(body_id));
                                match tcres.qpath_res(p, *hir_id) {
                                    hir::def::Res::Def(_, did) => did,
                                    res => panic!("Not a function? {res:?}"),
                                }
                            }
                            _ => panic!("Unsupported expression kind {:?}", e.kind),
                        };
                        self.marked_stmts
                            .insert(id, ((sink_matches, obj_type), e.span, did))
                            .is_none()
                    }
                }
            })
        }
    }

    /// Finds the functions that have been marked as targets.
    fn visit_fn(
        &mut self,
        fk: FnKind<'tcx>,
        fd: &'tcx rustc_hir::FnDecl<'tcx>,
        b: BodyId,
        s: Span,
        id: HirId,
    ) {
        match &fk {
            FnKind::ItemFn(ident, _, _) | FnKind::Method(ident, _)
                if self.should_analyze_function(id) =>
            {
                self.functions_to_analyze.push((*ident, b, fd));
            }
            _ => (),
        }

        // dispatch to recursive walk. This is probably unnecessary but if in
        // the future we decide to do something with nested items we may need
        // it.
        intravisit::walk_fn(self, fk, fd, b, s, id)
    }
}
