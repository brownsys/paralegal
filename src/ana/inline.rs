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

use std::{borrow::Cow, cell::RefCell, rc::Rc};

use crate::{
    consts, dbg,
    desc::*,
    ir::*,
    rust::*,
    sah::HashVerifications,
    utils::{PlaceExt, *},
    Either, HashMap, HashSet,
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
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_span::{symbol::Ident, Span, Symbol};

use flowistry::{
    indexed::IndexSet,
    infoflow::{FlowAnalysis, FlowDomain, NonTransitiveFlowDomain},
    mir::{
        aliases::Aliases,
        borrowck_facts::{self, CachedSimplifedBodyWithFacts},
        engine::AnalysisResults,
    },
};


impl<'tcx, 'g> InlineableCallDescriptor<'tcx, 'g> {
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
    pub fn translate_child_to_parent(
        &self,
        tcx: TyCtxt<'tcx>,
        parent_local_def_id: LocalDefId,
        child: mir::Place<'tcx>,
        mutated: bool,
        parent_body: &mir::Body<'tcx>,
    ) -> Option<mir::Place<'tcx>> {
        use mir::HasLocalDecls;
        use mir::ProjectionElem;
        if child.local == mir::RETURN_PLACE && child.projection.len() == 0 {
            if child
                .ty(self.simplified_callee_body.local_decls(), tcx)
                .ty
                .is_unit()
            {
                return None;
            }

            if let Some((dst, _)) = self.call_return {
                return Some(dst);
            }
        }

        if !flowistry::mir::utils::PlaceExt::is_arg(&child, self.simplified_callee_body)
            || (mutated && !child.is_indirect())
        {
            return None;
        }

        // For example, say we're calling f(_5.0) and child = (*_1).1 where
        // .1 is private to parent. Then:
        //    parent_toplevel_arg = _5.0
        //    parent_arg_projected = (*_5.0).1
        //    parent_arg_accessible = (*_5.0)

        let parent_toplevel_arg = self.call_arguments[child.local.as_usize() - 1]?;

        let mut projection = parent_toplevel_arg.projection.to_vec();
        let mut ty = parent_toplevel_arg.ty(parent_body.local_decls(), tcx);
        let parent_param_env = tcx.param_env(parent_local_def_id);
        let idx = 0; //self.remapper.strip_projection(child);
        if child.projection.len() < idx {
            return None;
        }
        for &elem in child.projection[idx..].iter() {
            ty = ty.projection_ty_core(tcx, parent_param_env, &elem, |_, field, fty| {
                debug!("ty: {ty:?}, child: {child:?}, elem: {elem:?}, field: {field:?}");
                if matches!(ty.ty.kind(), ty::TyKind::Generator(..)) {
                    fty
                } else {
                    ty.field_ty(tcx, field)
                }
            });
            let elem = match elem {
                ProjectionElem::Field(field, _) => ProjectionElem::Field(field, ty.ty),
                elem => elem,
            };
            projection.push(elem);
        }

        let parent_arg_projected = <Place as flowistry::mir::utils::PlaceExt>::make(
            parent_toplevel_arg.local,
            &projection,
            tcx,
        );

        Some(parent_arg_projected)
    }
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

    /// Memoization of non-transitive alias analysis
    flattening_helper: RefCell<DependencyFlatteningHelper<'tcx>>,
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
/// - Flowistry is a separate crate and so I wanted a way to control it that
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
///    [`crate::AnalysisCtrl::no_recursive_analysis`])
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
            flattening_helper: RefCell::new(DependencyFlatteningHelper::new(tcx)),
        }
    }

    /// This does the same as [`RecurseSelector`]. It's kind of difficult to
    /// reuse the recurse selector (because it gets moved into a `fluid_let` to
    /// control flowistry recursion), hence this reimplementation here.
    fn should_inline(&self, did: LocalDefId) -> bool {
        !self.analysis_opts.no_recursive_analysis
            && self.inline_selector.should_inline(self.tcx, did)
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
            under_construction: GlobalFlowGraph::default(),
        };

        use mir::visit::Visitor;

        inliner.visit_body(body);

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
    fn compute_call_only_flow(
        &self,
        body_id: BodyId,
        g: &GlobalFlowGraph<'tcx, 'g>,
    ) -> CallOnlyFlow<GlobalLocation<'g>> {
        debug!(
            "Shrinking global flow graph with {} states",
            g.location_states.len()
        );

        let tcx = self.tcx;

        let location_dependencies = g
            .location_states
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

                let deep_deps_for = |p: mir::Place<'tcx>| {
                    self.flattening_helper
                        .borrow_mut()
                        .deep_dependencies_of(*loc, g, p, &self.function_flows)
                };

                // Determine the control flow dependency for the location.
                let flows_borrow = self.function_flows.borrow();
                let flow_analysis = &flows_borrow
                    .get(&inner_body)
                    .unwrap()
                    .as_ref()
                    .unwrap()
                    .analysis
                    .analysis;
                let controlled_by = &flow_analysis
                    .control_dependencies
                    .dependent_on(inner_location.block);
                let mut ctrl_deps = HashSet::new();
                for block in controlled_by.iter().flat_map(|set| set.iter()) {
                    let mir_location = flow_analysis.body.terminator_loc(block);
                    // Get the terminator location and find all the places that it references, then call deep_deps to find the corresponding dependency locations.
                    let referenced_places = places_read(
                        tcx,
                        mir_location,
                        &flow_analysis.body.stmt_at(mir_location),
                        None,
                    );
                    for deps in referenced_places.map(deep_deps_for) {
                        ctrl_deps.extend(deps);
                    }
                }

                Some((
                    *loc,
                    CallDeps {
                        input_deps: args
                            .into_iter()
                            .map(|p| p.map_or_else(HashSet::new, deep_deps_for))
                            .collect(),
                        ctrl_deps,
                    },
                ))
            })
            .collect();

        let local_def_id = self.tcx.hir().body_owner_def_id(body_id);

        let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(self.tcx, local_def_id);
        let body = body_with_facts.simplified_body();
        let return_dependencies: HashSet<_> = body
            .basic_blocks()
            .iter_enumerated()
            .filter(|(_, bbdat)| matches!(bbdat.terminator().kind, TerminatorKind::Return))
            .map(|(i, _)| body.terminator_loc(i))
            .flat_map(|l| {
                self.flattening_helper.borrow_mut().deep_dependencies_of(
                    self.gli.globalize_location(l, body_id),
                    g,
                    Place::return_place(),
                    &self.function_flows
                )
            })
            .collect();
        debug!("Found {} return dependencies", return_dependencies.len());
        CallOnlyFlow {
            location_dependencies,
            return_dependencies,
        }
    }
}

use ty::RegionVid;

extern crate polonius_engine;

/// For some reason I can't find a canonical place where the `LocationIndex`
/// type from [`rustc_borrowck`] is exported. So instead I alias it here using
/// the [`polonius_engine::FactTypes`] trait through which it *must* be
/// exported.
///
/// Some of our type signatures need to refer to this type which this alias
/// makes easier.
type LocationIndex = <rustc_borrowck::consumers::RustcFacts as polonius_engine::FactTypes>::Point;

/// The constraint selector is essentially a closure. The function that it
/// encapsulates is [`Self::select`] and it is constructed with
/// [`Self::location_based`].
///
/// This type, as a selector, is handed to
/// [`flowistry::mir::aliases::Aliases::build_with_fact_selection`]. This is
/// done during construction of the [`CallOnlyFlow`] where we require a
/// non-transitive alias analysis. This struct facilitates this by severing
/// lifetime entailments over function calls which makes the alias analysis
/// non-transitive with respect to function calls.
struct ConstraintSelector<'tcx, 'a> {
    body_with_facts: &'a BodyWithBorrowckFacts<'tcx>,
}

impl<'a, 'tcx> ConstraintSelector<'tcx, 'a> {
    /// Now the only constructor for this type
    fn location_based(body_with_facts: &'a BodyWithBorrowckFacts<'tcx>) -> Self {
        Self { body_with_facts }
    }

    /// Selects whether to keep a fact from `BodyWithBorrowckFacts.all_facts.subset_base`
    fn select(&self, _: RegionVid, _: RegionVid, idx: LocationIndex) -> bool {
        use rustc_borrowck::consumers::RichLocation;
        let rich_loc = self.body_with_facts.location_table.to_location(idx);
        let loc = match rich_loc {
            RichLocation::Mid(l) => l,
            RichLocation::Start(l) => l,
        };
        let stmt = self.body_with_facts.body.stmt_at(loc);
        !matches!(
            stmt,
            Either::Right(Terminator {
                kind: TerminatorKind::Call { .. },
                ..
            })
        )
    }
}

/// A memoizing helper for resolving dependencies of a [`Place`] during
/// [`GlobalFlowConstructor::compute_call_only_flow`].
///
/// It constructs [`Aliases`] for the provided body (a computation that is
/// memoized internally). The aliases are constructed without considering
/// region entailments (essentially "outlives" constraints on the lifetimes in
/// the function) that are caused by function calls. This is deliberate and
/// causes the resulting [`Aliases`] to act non-transitively with respect to
/// function calls.
///
/// Lastly we use the computed aliases to call `aliases.reachable_values(p)` where `p` is the place argument that was provided.
pub struct DependencyFlatteningHelper<'tcx> {
    memoized_analyses: HashMap<LocalDefId, Aliases<'tcx, 'tcx>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> DependencyFlatteningHelper<'tcx> {
    /// Construct a new helper with an empty memoization.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            memoized_analyses: HashMap::new(),
            tcx,
        }
    }

    /// The reachable places for `p` in `body_with_facts` depending on the
    /// setting if `self.use_reachable_places`.
    ///
    /// If the configuration says to use [`Aliases::reachable_values`] then this
    /// may compute [`Aliases`] for the body, optionally discarding function
    /// call locations from the set of borrowcheck facts, see documentation on
    /// [`Self`] for more information.
    pub fn reachable_values(
        &mut self,
        body_with_facts: &'tcx CachedSimplifedBodyWithFacts<'tcx>,
        def_id: LocalDefId,
        p: mir::Place<'tcx>,
    ) -> Vec<Place<'tcx>> {
        let new_aliases = self.get_aliases(def_id, body_with_facts);
        let a = new_aliases
            .reachable_values(p, ast::Mutability::Not)
            .iter()
            .flat_map(|&p| new_aliases.children(p).into_iter())
            //.cloned()
            //.filter(|p| p.is_direct(body_with_facts.borrowckd_body()))
            .collect::<Vec<_>>();

        debug!(
            "Determined the reachable places for {p:?} are {:?} and also conflicts {a:?}",
            new_aliases.reachable_values(p, ast::Mutability::Not)
        );
        debug!("Aliases would have been {:?}", new_aliases.aliases(p));
        a
    }

    /// Memoized [`Aliases::build_with_fact_selection`].
    fn get_aliases(
        &mut self,
        def_id: LocalDefId,
        body_with_facts: &'tcx CachedSimplifedBodyWithFacts<'tcx>,
    ) -> &Aliases<'tcx, 'tcx> {
        self.memoized_analyses.entry(def_id).or_insert_with(|| {
            let selector = ConstraintSelector::location_based(body_with_facts.body_with_facts());
            Aliases::build_with_fact_selection(
                self.tcx,
                def_id.to_def_id(),
                body_with_facts,
                |r1, r2, idx| selector.select(r1, r2, idx),
            )
        })
    }

    /// Perform a depth-first search up the dependency tree formed from looking up
    /// the [`places_read`] at a location in `g`, starting from `loc`.
    ///
    /// Terminates on each branch when a location `l` is encountered that does not
    /// satisfy `matches!(Keep::from_global_location(tcx, l), Keep::Reject(_))`.
    ///
    /// In addition the set of places that is considered "read" for `loc` (the
    /// initial location) is
    /// [`reachable_values(p)`](Self::reachable_values)
    /// This means we consider all subplaces as also read. This only makes sense for
    /// function calls, hence this should only be called on locations that represent
    /// function calls.
    pub fn deep_dependencies_of<'g>(
        &mut self,
        loc: GlobalLocation<'g>,
        g: &GlobalFlowGraph<'tcx, 'g>,
        p: mir::Place<'tcx>,
        flows: &FunctionFlows<'tcx, 'g>,
    ) -> HashSet<GlobalLocation<'g>> {
        let tcx = self.tcx;
        let slf = RefCell::new(self);
        debug!("Flattening {p:?} @ {loc}");
        let (inner_loc, inner_body) = loc.innermost_location_and_body();
        let def_id = tcx.hir().body_owner_def_id(inner_body);
        let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, def_id);
        let stmt = body_with_facts.simplified_body().stmt_at(inner_loc);
        if !matches!(
            stmt,
            Either::Right(Terminator {
                kind: TerminatorKind::Call { .. },
                ..
            }) | Either::Right(Terminator {
                kind: TerminatorKind::Return,
                ..
            })
        ) {
            warn!("`deep_dependencies_of` was called on non-function-call location {} with statement {:?}", loc, stmt);
        }
        // Get the combined dependencies for `places` at the
        // location `loc` also taking into account provenance.
        let deps_for_places = |loc: GlobalLocation<'g>, places: &[Place<'tcx>]| {
            if let Some(deps) = g.location_states.get(&loc) {
                places
                    .iter()
                    //.flat_map(|&origin| origin.provenance(tcx))
                    .flat_map(|&projection| {
                        let normalized = flowistry::mir::utils::PlaceExt::normalize(
                                &projection,
                                tcx,
                                tcx.hir()
                                    .body_owner_def_id(loc.innermost_location_and_body().1)
                                    .to_def_id(),
                            );
                        let (new_place, deps) = match deps.resolve(normalized) {
                            Translation::Found((new_place, deps)) => {
                                debug!("      Translated {normalized:?} to {new_place:?}");
                                (new_place, Box::new(deps) as Box<dyn Iterator<Item=GlobalLocation<'g>>>)
                            },
                            Translation::Unchanged(deps) => (projection, Box::new(deps) as Box<_>),
                            Translation::Missing => {
                                let body_id = loc.innermost_location_and_body().1;
                                let def_id = tcx.hir().body_owner_def_id(body_id);
                                let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, def_id);
                                let mut slf = slf.borrow_mut();
                                let flow = flows.borrow()[&body_id].clone().unwrap();
                                let aliases = &flow.analysis.analysis.aliases;
                                //slf.get_aliases(def_id, body_with_facts);
                                warn!("      Could not translate {normalized:?}. Place aliases are {:?}, normalized aliases are {:?}", aliases.aliases(projection), aliases.aliases(normalized));
                                (projection, Box::new(std::iter::empty()) as Box<_>)
                            }
                        };
                        deps.map(move |d| (new_place, d))
                    })
                    .collect::<Vec<(Place<'tcx>, GlobalLocation<'g>)>>()
            } else {
                debug!("    No dependencies found");
                vec![]
            }
        };

        // See https://www.notion.so/justus-adam/Call-chain-analysis-26fb36e29f7e4750a270c8d237a527c1#b5dfc64d531749de904a9fb85522949c
        let reachable_places = slf.borrow_mut().reachable_values(body_with_facts, def_id, p);
        let mut queue = deps_for_places(loc, &reachable_places);
        let mut seen = HashSet::new();
        let mut deps = HashSet::new();

        // A reverse dfs traversing the flowistry tensor which terminates every time we find a function call.
        while let Some((place, location)) = queue.pop() {
            debug!("  considering {place:?} at {location}");
            // A special situation has ocurred. We've hit a translation boundary
            // (either an argument or a call site of an inlined function). This
            // causes a translation of the place, but otherwise this location must
            // be rejected so we translate, resolve and move on.
            if g.location_states.get(&location).map(|s| s.is_translated()) == Some(true) {
                debug!("    Is crossing function boundary");
                // Don't insert this location into `seen`, because we might cross
                // this boundary multiple times with different places
                queue.extend(deps_for_places(location, &[place]));
            } else {
                match Keep::from_global_location(tcx, location) {
                    Keep::Keep(..) | Keep::Argument(_) => {
                        debug!(
                            "  Found dependency from {p:?} on {location} via the last place {place:?}"
                        );
                        deps.insert(location);
                    }
                    Keep::Reject(stmt_at_loc) if !seen.contains(&location) => {
                        debug!("    Rejecting");
                        seen.insert(location);
                        if let Some(stmt) = stmt_at_loc {
                            queue.extend(deps_for_places(
                                location,
                                &places_read(
                                    tcx,
                                    location.innermost_location_and_body().0,
                                    &stmt,
                                    Some(place),
                                )
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
}

/// A struct responsible for creating a global flow matrix for one [`mir::Body`],
/// inlining all callees (that are configured to be inlined). It is a similar
/// idea to `GlobalFlowConstructor` (in fact it wraps one) that bundles together
/// all information needed to inline into one [`mir::Body`] so that we can split
/// it into helper functions which all have access to this information.
///
/// ## Usage
///
/// The function inliner implements [`mir::visit::Visitor`] that should be applied
/// to only the same [`mir::Body`] this struct was initialized with.
///
/// The methods are currently split into the visit methods that actually modify
/// `self.under_construction` and helper methods such as
/// `self.handle_regular_location` that take an immutable `&self` and return
/// their computed results instead of appending them directly to
/// `under_construction`. This is so that we can use these functions
/// agnostically and later make a determination about where to insert their
/// results. For instance the result of `handle_regular_location` is both
/// inserted into `location_states` but also added to `return_state` when we are
/// handling a terminator. However [`Self::handle_regular_location`] itself does not
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
        use flowistry::mir::utils::PlaceExt;
        matrix
            .rows()
            .map(|(place, dep_set)| {
                (
                    place.normalize(self.tcx(), self.local_def_id.to_def_id()),
                    self.make_row_global(dep_set),
                )
            })
            .collect()
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
    ) -> Result<InlineableCallDescriptor<'tcx, 'g>, &'static str> {
        t.as_fn_and_args().and_then(|(p, mut args, call_return)| {
            let (p, call_arguments) = if Some(p) != self.tcx().lang_items().from_generator_fn() {
                (p, args)
            } else {
                let closure = args
                    .pop()
                    .expect("Expected one closure argument")
                    .expect("Expected non-const closure argument");
                debug_assert!(args.is_empty(), "Expected only one argument");
                debug_assert!(closure.projection.is_empty());
                let closure_fn = if let ty::TyKind::Generator(gid, _, _) =
                    self.body.local_decls[closure.local].ty.kind()
                {
                    *gid
                } else {
                    unreachable!("Expected Generator")
                };
                (closure_fn, vec![Some(closure), None])
            };

            self.tcx()
                .hir()
                .get_if_local(p)
                .ok_or("non-local node")
                .and_then(|node| {
                    let (_callee_id, callee_local_id, callee_body_id) = node
                        .as_fn(self.tcx())
                        .unwrap_or_else(|| panic!("Expected local function node, got {node:?}"));
                    if self.flow_constructor.should_inline(callee_local_id) {
                        Ok(())
                    } else {
                        Err("Inline selector was false")
                    }?;
                    let callee_flow = self
                        .flow_constructor
                        .compute_granular_global_flows(callee_body_id)
                        .ok_or("is recursive")?;
                    let simplified_callee_body =
                        borrowck_facts::get_body_with_borrowck_facts(self.tcx(), callee_local_id)
                            .simplified_body();
                    Ok(InlineableCallDescriptor {
                        callee_flow,
                        callee_body_id,
                        simplified_callee_body,
                        call_arguments,
                        call_return,
                    })
                })
        })
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

    fn make_place_translation_base<'a>(
        &'a self, 
        descriptor: &'a InlineableCallDescriptor<'tcx, 'g>,
    ) -> Vec<(mir::Place<'tcx>, mir::Place<'tcx>)> {
        descriptor
            .callee_flow
            .flow
            .location_states
            .iter()
            .filter_map(|(loc, matrix)| {
                (loc.is_at_root() && !matrix.is_translated()).then_some(matrix)
            })
            .flat_map(|s| s.keys())
            .collect::<HashSet<mir::Place<'tcx>>>()
            .into_iter()
            .filter_map(|child| {
                Some((
                    child,
                    descriptor.translate_child_to_parent(
                        self.tcx(),
                        self.local_def_id,
                        child,
                        false,
                        self.body,
                    )?,
                ))
            })
            .collect()
    }

    /// Create a [`PlaceTranslationTable`] that maps places from the callee
    /// (`inner_flow`) to the caller (`self.body`).
    fn create_callee_to_caller_translation_table(
        &self,
        descriptor: &InlineableCallDescriptor<'tcx, 'g>,
    ) -> PlaceTranslationTable<'tcx> {
        self.make_place_translation_base(descriptor)
            .into_iter()
            .collect::<HashMap<_, _>>()
    }

    /// Create a [`PlaceTranslationTable`] that maps places from the caller
    /// (`self.body`) to places in the callee (`inner_flow`).
    fn create_caller_to_callee_translation_table(
        &self,
        descriptor: &InlineableCallDescriptor<'tcx, 'g>,
    ) -> PlaceTranslationTable<'tcx> {
        self.make_place_translation_base(descriptor)
            .into_iter()
            .flat_map(|(child, parent)|{

                let alias_info = &self.from_flowistry.analysis.aliases;
                alias_info.aliases(parent).iter()
                    .map(move |&parent| (parent, child))
            })
            .collect()

        // descriptor
        //     .callee_flow
        //     .flow
        //     .location_states
        //     .iter()
        //     .filter_map(|(loc, matrix)| {
        //         (loc.is_at_root() && !matrix.is_translated()).then_some(matrix)
        //     })
        //     .flat_map(|s| s.keys())
        //     .collect::<HashSet<_>>()
        //     .into_iter()
        //     .flat_map(|child| {
        //         let parent = descriptor.translate_child_to_parent(
        //             self.tcx(),
        //             self.local_def_id,
        //             child,
        //             true,
        //             self.body,
        //         );
        //         let alias_info = &self.from_flowistry.analysis.aliases;
        //         parent
        //             .into_iter()
        //             .flat_map(|p| alias_info.aliases(p).iter())
        //             .map(move |&parent| (parent, child))
        //     })
        //     .collect::<HashMap<_, _>>()
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

/// This is the data structure returned by
/// [`FunctionInliner::inner_flow_for_terminator`] which contains the
/// information needed for further inlining. See the documentation for
/// the fields for more information.
struct InlineableCallDescriptor<'tcx, 'g> {
    /// is the fine grained, inlined data flow we have calculated for
    /// `callee_body_id`. All locations in this flow are relative to that
    /// function.
    callee_flow: Rc<FunctionFlow<'tcx, 'g>>,
    /// Obviously the id for the called function body.
    callee_body_id: BodyId,
    /// This is the version of the body flowistry ran on.
    simplified_callee_body: &'tcx mir::Body<'tcx>,
    /// These are the arguments this function is called with. These are either
    /// the arguments as we've parsed them out of the [`Terminator`], but in
    /// case of an `async` closure we pass an additional [`None`] to respect the
    /// closure signature.
    call_arguments: Vec<Option<mir::Place<'tcx>>>,
    /// Is the return place as we found it in the [`Terminator`].
    call_return: Option<(mir::Place<'tcx>, mir::BasicBlock)>,
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
        if let Ok(desc) = self.inner_flow_for_terminator(terminator) {
            debug!(
                "Creating callee {:?} to caller {} translation table",
                terminator.kind,
                self.tcx()
                    .opt_item_name(self.local_def_id.to_def_id())
                    .unwrap_or(Symbol::intern("unknown"))
            );
            // A translation table from places in `inner_flow` to places from
            // `self.body` by lining them up at the arguments.
            //
            // Constructed by optimistically translating every place in the
            // callee to a place in the caller. This allows us to uphold the
            // invariant that when tracing dependencies a local place does not
            // immediately cross into a parent, but first into such an argument
            // location where it can get translated.
            let parent_translation_matrix = self.create_callee_to_caller_translation_table(&desc);
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
                desc.callee_flow
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
            let argument_locations = (1..=desc.call_arguments.len()).into_iter().map(|a| {
                let global_call_site = gli.globalize_location(
                    mir::Location {
                        block: mir::BasicBlock::from_usize(
                            desc.simplified_callee_body.basic_blocks().len(),
                        ),
                        statement_index: a,
                    },
                    desc.callee_body_id,
                );
                let global_arg_loc = make_relative_location(location, global_call_site);
                (global_arg_loc, parent_dep_matrix.clone())
            });

            debug!("Creating caller to callee translation table");

            // Lastly we create a location for this call site. This is also a
            // special, translating location and represents the return state
            // from calling `inner_flow` at this call site (see `TranslatedDepMatrix`).
            let call_site_location = (
                gli.globalize_location(location, root_function),
                TranslatedDepMatrix::translated(
                    relativize_global_dep_matrix(
                        &desc.callee_flow.flow.return_state,
                        local_relativizer,
                    ),
                    self.create_caller_to_callee_translation_table(&desc),
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
                        .or_insert_with(HashSet::new)
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
/// during [`GlobalFlowConstructor::compute_call_only_flow`]. The main way to
/// use this struct is with the `from_location` function which also has
/// additional documentation.
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
        if !location.is_real(body_with_facts.simplified_body()) {
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
    pub fn compute<P: InlineSelector + Clone + 'static>(
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

        let reduced_flow = constructor.compute_call_only_flow(body_id, &granular_flow.flow);
        debug!(
            "Constructed reduced flow of {} locations\n{:?}",
            reduced_flow.location_dependencies.len(),
            reduced_flow.location_dependencies.keys()
        );
        Self {
            root_function: body_id,
            function_flows: constructor.function_flows,
            reduced_flow,
        }
    }
}


