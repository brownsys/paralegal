use std::{borrow::Cow, collections::HashSet, iter, rc::Rc};

use df::{fmt::DebugWithContext, Analysis, JoinSemiLattice};
use either::Either;
use flowistry::mir::placeinfo::PlaceInfo;
use flowistry_pdg::{CallString, GlobalLocation, RichLocation};
use itertools::Itertools;
use log::{debug, log_enabled, trace, Level};
use petgraph::graph::DiGraph;

use rustc_abi::VariantIdx;
use rustc_borrowck::consumers::{places_conflict, BodyWithBorrowckFacts, PlaceConflictBias};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        visit::Visitor, AggregateKind, BasicBlock, Body, Location, Operand, Place, PlaceElem,
        Rvalue, Statement, Terminator, TerminatorEdges, TerminatorKind, RETURN_PLACE,
    },
    ty::{GenericArg, List, ParamEnv, Ty, TyCtxt, TyKind},
};
use rustc_mir_dataflow::{self as df};
use rustc_span::ErrorGuaranteed;
use rustc_utils::cache::Cache;
use rustc_utils::{
    mir::{borrowck_facts, control_dependencies::ControlDependencies},
    BodyExt, PlaceExt,
};

use super::async_support::*;
use super::calling_convention::*;
use super::graph::{DepEdge, DepGraph, DepNode};
use super::utils::{self, FnResolution};
use crate::{
    graph::{SourceUse, TargetUse},
    utils::is_non_default_trait_method,
};
use crate::{
    mutation::{ModularMutationVisitor, Mutation},
    try_resolve_function,
};

/// Whether or not to skip recursing into a function call during PDG construction.
#[derive(Debug)]
pub enum SkipCall {
    /// Skip the function, and perform a modular approxmation of its effects.
    Skip,

    /// Recurse into the function as normal.
    NoSkip,
}

/// A fake effect to insert into the PDG upon a function call.
#[derive(Debug)]
pub struct FakeEffect<'tcx> {
    /// The place (in the *callee*!) subject to a fake effect.
    pub place: Place<'tcx>,

    /// The kind of fake effect to insert into the PDG.
    pub kind: FakeEffectKind,
}

/// The kind of fake effect to insert into the PDG.
#[derive(Debug)]
pub enum FakeEffectKind {
    /// A fake read to an argument of a function call.
    ///
    /// For example, a fake read to argument `_1` of the call `f(_5)`
    /// would add an edge `_5@main::fcall -> _1@main->f::START`.
    Read,

    /// A fake write to an argument of a function call.
    ///
    /// For example, a fake write to argument `(*_1)` of the call `f(&mut _5)`
    /// would add an edge `_5@main::<before> -> _5@main::fcall`.
    Write,
}

/// User-provided changes to the default PDG construction behavior for function calls.
///
/// Construct [`CallChanges`] via [`CallChanges::default`].
#[derive(Debug)]
pub struct CallChanges<'tcx> {
    skip: SkipCall,
    fake_effects: Vec<FakeEffect<'tcx>>,
}

impl<'tcx> CallChanges<'tcx> {
    /// Inidicate whether or not to skip recursing into the given function.
    pub fn with_skip(self, skip: SkipCall) -> Self {
        CallChanges { skip, ..self }
    }

    /// Provide a set of fake effect to insert into the PDG.
    pub fn with_fake_effects(self, fake_effects: Vec<FakeEffect<'tcx>>) -> Self {
        CallChanges {
            fake_effects,
            ..self
        }
    }
}

impl Default for CallChanges<'_> {
    fn default() -> Self {
        CallChanges {
            skip: SkipCall::NoSkip,
            fake_effects: vec![],
        }
    }
}

/// Information about the function being called.
pub struct CallInfo<'tcx> {
    /// The potentially-monomorphized resolution of the callee.
    pub callee: FnResolution<'tcx>,

    /// If the callee is an async closure created by an `async fn`, this is the
    /// `async fn` item.
    pub async_parent: Option<FnResolution<'tcx>>,

    /// The call-stack up to the current call site.
    pub call_string: CallString,

    /// Would the PDG for this function be served from the cache.
    pub is_cached: bool,
}

/// Top-level parameters to PDG construction.
#[derive(Clone)]
pub struct PdgParams<'tcx> {
    tcx: TyCtxt<'tcx>,
    root: FnResolution<'tcx>,
    call_change_callback: Option<Rc<dyn CallChangeCallback<'tcx> + 'tcx>>,
    dump_mir: bool,
}

pub trait CallChangeCallback<'tcx> {
    fn on_inline(&self, info: CallInfo<'tcx>) -> CallChanges<'tcx>;

    fn on_inline_miss(
        &self,
        _resolution: FnResolution<'tcx>,
        _loc: Location,
        _under_analysis: FnResolution<'tcx>,
        _call_string: Option<CallString>,
        _reason: InlineMissReason,
    ) {
    }
}

pub struct CallChangeCallbackFn<'tcx> {
    f: Box<dyn Fn(CallInfo<'tcx>) -> CallChanges<'tcx> + 'tcx>,
}

impl<'tcx> CallChangeCallbackFn<'tcx> {
    pub fn new(f: impl Fn(CallInfo<'tcx>) -> CallChanges<'tcx> + 'tcx) -> Self {
        Self { f: Box::new(f) }
    }
}

impl<'tcx> CallChangeCallback<'tcx> for CallChangeCallbackFn<'tcx> {
    fn on_inline(&self, info: CallInfo<'tcx>) -> CallChanges<'tcx> {
        (self.f)(info)
    }
}

#[derive(Debug)]
pub enum InlineMissReason {
    Async(String),
}

fn manufacture_substs_for(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
) -> Result<&List<GenericArg<'_>>, ErrorGuaranteed> {
    use rustc_middle::ty::{
        Binder, BoundRegionKind, DynKind, ExistentialPredicate, ExistentialProjection,
        ExistentialTraitRef, GenericParamDefKind, ImplPolarity, ParamTy, Region, TraitPredicate,
    };

    let generics = tcx.generics_of(function);
    let predicates = tcx.predicates_of(function).instantiate_identity(tcx);
    let types = (0..generics.count()).map(|gidx| {
        let param = generics.param_at(gidx, tcx);
        if let Some(default_val) = param.default_value(tcx) {
            return Ok(default_val.instantiate_identity());
        }
        match param.kind {
            // I'm not sure this is correct. We could probably return also "erased" or "static" here.
            GenericParamDefKind::Lifetime => {
                return Ok(GenericArg::from(Region::new_free(
                    tcx,
                    function.to_def_id(),
                    BoundRegionKind::BrAnon(None),
                )))
            }
            GenericParamDefKind::Const { .. } => {
                return Err(tcx.sess.span_err(
                    tcx.def_span(param.def_id),
                    "Cannot use constants as generic parameters in controllers",
                ))
            }
            GenericParamDefKind::Type { .. } => (),
        };

        let param_as_ty = ParamTy::for_def(param);
        let constraints = predicates.predicates.iter().filter_map(|clause| {
            let pred = if let Some(trait_ref) = clause.as_trait_clause() {
                if trait_ref.polarity() != ImplPolarity::Positive {
                    return None;
                };
                let Some(TraitPredicate { trait_ref, .. }) = trait_ref.no_bound_vars() else {
                    return Some(Err(tcx.sess.span_err(
                        tcx.def_span(param.def_id),
                        format!("Trait ref had binder {trait_ref:?}"),
                    )));
                };
                if !matches!(trait_ref.self_ty().kind(), TyKind::Param(p) if *p == param_as_ty) {
                    return None;
                };
                Some(ExistentialPredicate::Trait(
                    ExistentialTraitRef::erase_self_ty(tcx, trait_ref),
                ))
            } else if let Some(pred) = clause.as_projection_clause() {
                let pred = pred.no_bound_vars()?;
                if !matches!(pred.self_ty().kind(), TyKind::Param(p) if *p == param_as_ty) {
                    return None;
                };
                Some(ExistentialPredicate::Projection(
                    ExistentialProjection::erase_self_ty(tcx, pred),
                ))
            } else {
                None
            }?;

            Some(Ok(Binder::dummy(pred)))
        });
        let ty = Ty::new_dynamic(
            tcx,
            tcx.mk_poly_existential_predicates_from_iter(constraints)?,
            Region::new_free(tcx, function.to_def_id(), BoundRegionKind::BrAnon(None)),
            DynKind::Dyn,
        );
        Ok(GenericArg::from(ty))
    });
    tcx.mk_args_from_iter(types)
}

impl<'tcx> PdgParams<'tcx> {
    /// Must provide the [`TyCtxt`] and the [`LocalDefId`] of the function that is the root of the PDG.
    pub fn new(tcx: TyCtxt<'tcx>, root: LocalDefId) -> Result<Self, ErrorGuaranteed> {
        let root = try_resolve_function(
            tcx,
            root.to_def_id(),
            tcx.param_env_reveal_all_normalized(root),
            manufacture_substs_for(tcx, root)?,
        );
        Ok(PdgParams {
            tcx,
            root,
            call_change_callback: None,
            dump_mir: false,
        })
    }

    pub fn with_dump_mir(mut self, dump_mir: bool) -> Self {
        self.dump_mir = dump_mir;
        self
    }

    /// Provide a callback for changing the behavior of how the PDG generator manages function calls.
    ///
    /// Currently, this callback can either indicate that a function call should be skipped (i.e., not recursed into),
    /// or indicate that a set of fake effects should occur at the function call. See [`CallChanges`] for details.
    ///
    /// For example, in this code:
    ///
    /// ```
    /// fn incr(x: i32) -> i32 { x + 1 }
    /// fn main() {
    ///   let a = 0;
    ///   let b = incr(a);
    /// }
    /// ```
    ///
    /// When inspecting the call `incr(a)`, the callback will be called with `f({callee: incr, call_string: [main]})`.
    /// You could apply a hard limit on call string length like this:
    ///
    /// ```
    /// # #![feature(rustc_private)]
    /// # extern crate rustc_middle;
    /// # use flowistry_pdg_construction::{PdgParams, SkipCall, CallChanges};
    /// # use rustc_middle::ty::TyCtxt;
    /// # const THRESHOLD: usize = 5;
    /// # fn f<'tcx>(tcx: TyCtxt<'tcx>, params: PdgParams<'tcx>) -> PdgParams<'tcx> {
    /// params.with_call_change_callback(|info| {
    ///   let skip = if info.call_string.len() > THRESHOLD {
    ///     SkipCall::Skip
    ///   } else {
    ///     SkipCall::NoSkip
    ///   };
    ///   CallChanges::default().with_skip(skip)
    /// })
    /// # }
    /// ```
    pub fn with_call_change_callback(self, f: impl CallChangeCallback<'tcx> + 'tcx) -> Self {
        PdgParams {
            call_change_callback: Some(Rc::new(f)),
            ..self
        }
    }
}

#[derive(PartialEq, Eq, Default, Clone, Debug)]
pub struct PartialGraph<'tcx> {
    nodes: FxHashSet<DepNode<'tcx>>,
    edges: FxHashSet<(DepNode<'tcx>, DepNode<'tcx>, DepEdge)>,
    last_mutation: FxHashMap<Place<'tcx>, FxHashSet<RichLocation>>,
}

impl<C> DebugWithContext<C> for PartialGraph<'_> {}

impl<'tcx> df::JoinSemiLattice for PartialGraph<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let b1 = utils::hashset_join(&mut self.edges, &other.edges);
        let b2 = utils::hashset_join(&mut self.nodes, &other.nodes);
        let b3 = utils::hashmap_join(
            &mut self.last_mutation,
            &other.last_mutation,
            utils::hashset_join,
        );
        b1 || b2 || b3
    }
}

pub(crate) struct CallingContext<'tcx> {
    pub(crate) call_string: CallString,
    pub(crate) param_env: ParamEnv<'tcx>,
    pub(crate) call_stack: Vec<DefId>,
}

type PdgCache<'tcx> = Rc<Cache<CallString, Rc<PartialGraph<'tcx>>>>;

pub struct GraphConstructor<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) params: PdgParams<'tcx>,
    body_with_facts: &'tcx BodyWithBorrowckFacts<'tcx>,
    pub(crate) body: Cow<'tcx, Body<'tcx>>,
    pub(crate) def_id: LocalDefId,
    place_info: PlaceInfo<'tcx>,
    control_dependencies: ControlDependencies<BasicBlock>,
    pub(crate) body_assignments: utils::BodyAssignments,
    pub(crate) calling_context: Option<CallingContext<'tcx>>,
    start_loc: FxHashSet<RichLocation>,
    pub(crate) async_info: Rc<AsyncInfo>,
    pub(crate) pdg_cache: PdgCache<'tcx>,
}

fn as_arg<'tcx>(place: Place<'tcx>, body: &Body<'tcx>) -> Option<u8> {
    (body.local_kind(place.local) == rustc_middle::mir::LocalKind::Arg)
        .then(|| place.local.as_u32() as u8 - 1)
}

#[derive(Debug)]
enum Inputs<'tcx> {
    Unresolved {
        places: Vec<(Place<'tcx>, Option<u8>)>,
    },
    Resolved {
        node: DepNode<'tcx>,
        node_use: SourceUse,
    },
}

impl<'tcx> GraphConstructor<'tcx> {
    /// Creates a [`GraphConstructor`] at the root of the PDG.
    pub fn root(params: PdgParams<'tcx>) -> Self {
        let tcx = params.tcx;
        GraphConstructor::new(
            params,
            None,
            AsyncInfo::make(tcx).expect("async functions are not defined"),
            &PdgCache::default(),
        )
    }

    /// Creates [`GraphConstructor`] for a function resolved as `fn_resolution` in a given `calling_context`.
    pub(crate) fn new(
        params: PdgParams<'tcx>,
        calling_context: Option<CallingContext<'tcx>>,
        async_info: Rc<AsyncInfo>,
        pdg_cache: &PdgCache<'tcx>,
    ) -> Self {
        let tcx = params.tcx;
        let def_id = params.root.def_id().expect_local();
        let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, def_id);
        let param_env = match &calling_context {
            Some(cx) => cx.param_env,
            None => ParamEnv::reveal_all(),
        };
        let body = params
            .root
            .try_monomorphize(tcx, param_env, &body_with_facts.body);

        if params.dump_mir {
            use std::io::Write;
            let path = tcx.def_path_str(def_id) + ".mir";
            let mut f = std::fs::File::create(path.as_str()).unwrap();
            write!(f, "{}", body.to_string(tcx).unwrap()).unwrap();
            debug!("Dumped debug MIR {path}");
        }

        let place_info = PlaceInfo::build(tcx, def_id.to_def_id(), body_with_facts);
        let control_dependencies = body.control_dependencies();

        let mut start_loc = FxHashSet::default();
        start_loc.insert(RichLocation::Start);

        let body_assignments = utils::find_body_assignments(&body);
        let pdg_cache = Rc::clone(pdg_cache);

        GraphConstructor {
            tcx,
            params,
            body_with_facts,
            body,
            place_info,
            control_dependencies,
            start_loc,
            def_id,
            calling_context,
            body_assignments,
            async_info,
            pdg_cache,
        }
    }

    /// Creates a [`GlobalLocation`] at the current function.
    fn make_global_loc(&self, location: impl Into<RichLocation>) -> GlobalLocation {
        GlobalLocation {
            function: self.def_id,
            location: location.into(),
        }
    }

    pub(crate) fn calling_context_for(
        &self,
        call_stack_extension: DefId,
        location: Location,
    ) -> CallingContext<'tcx> {
        CallingContext {
            call_string: self.make_call_string(location),
            param_env: self.tcx.param_env_reveal_all_normalized(self.def_id),
            call_stack: match &self.calling_context {
                Some(cx) => {
                    let mut cx = cx.call_stack.clone();
                    cx.push(call_stack_extension);
                    cx
                }
                None => vec![],
            },
        }
    }

    pub(crate) fn pdg_params_for_call(&self, root: FnResolution<'tcx>) -> PdgParams<'tcx> {
        PdgParams {
            root,
            ..self.params.clone()
        }
    }

    /// Creates a [`CallString`] with the current function at the root,
    /// with the rest of the string provided by the [`CallingContext`].
    fn make_call_string(&self, location: impl Into<RichLocation>) -> CallString {
        let global_loc = self.make_global_loc(location);
        match &self.calling_context {
            Some(cx) => cx.call_string.push(global_loc),
            None => CallString::single(global_loc),
        }
    }

    fn make_dep_node(
        &self,
        place: Place<'tcx>,
        location: impl Into<RichLocation>,
    ) -> DepNode<'tcx> {
        DepNode::new(place, self.make_call_string(location), self.tcx, &self.body)
    }

    /// Returns all pairs of `(src, edge)`` such that the given `location` is control-dependent on `edge`
    /// with input `src`.
    fn find_control_inputs(&self, location: Location) -> Vec<(DepNode<'tcx>, DepEdge)> {
        let mut blocks_seen = HashSet::<BasicBlock>::from_iter(Some(location.block));
        let mut block_queue = vec![location.block];
        let mut out = vec![];
        while let Some(block) = block_queue.pop() {
            if let Some(ctrl_deps) = self.control_dependencies.dependent_on(block) {
                for dep in ctrl_deps.iter() {
                    let ctrl_loc = self.body.terminator_loc(dep);
                    let Terminator {
                        kind: TerminatorKind::SwitchInt { discr, .. },
                        ..
                    } = self.body.basic_blocks[dep].terminator()
                    else {
                        if blocks_seen.insert(dep) {
                            block_queue.push(dep);
                        }
                        continue;
                    };
                    let Some(ctrl_place) = discr.place() else {
                        continue;
                    };
                    let at = self.make_call_string(ctrl_loc);
                    let src = DepNode::new(ctrl_place, at, self.tcx, &self.body);
                    let edge = DepEdge::control(at, SourceUse::Operand, TargetUse::Assign);
                    out.push((src, edge));
                }
            }
        }
        out
    }

    /// Returns the aliases of `place`. See [`PlaceInfo::aliases`] for details.
    pub(crate) fn aliases(&self, place: Place<'tcx>) -> impl Iterator<Item = Place<'tcx>> + '_ {
        // MASSIVE HACK ALERT:
        // The issue is that monomorphization erases regions, due to how it's implemented in rustc.
        // However, Flowistry's alias analysis uses regions to figure out aliases.
        // To workaround this incompatibility, when we receive a monomorphized place, we try to
        // recompute its type in the context of the original region-containing body as far as possible.
        //
        // For example, say _2: (&'0 impl Foo,) in the original body and _2: (&(i32, i32),) in the monomorphized body.
        // Say we ask for aliases (*(_2.0)).0. Then we will retype ((*_2.0).0).0 and receive back (*_2.0: &'0 impl Foo).
        // We can ask for the aliases in the context of the original body, receiving e.g. {_1}.
        // Then we reproject the aliases with the remaining projection, to create {_1.0}.
        //
        // This is a massive hack bc it's inefficient and I'm not certain that it's sound.
        let place_retyped = utils::retype_place(
            place,
            self.tcx,
            &self.body_with_facts.body,
            self.def_id.to_def_id(),
        );
        self.place_info.aliases(place_retyped).iter().map(|alias| {
            let mut projection = alias.projection.to_vec();
            projection.extend(&place.projection[place_retyped.projection.len()..]);
            Place::make(alias.local, &projection, self.tcx)
        })
    }

    /// Returns all nodes `src` such that `src` is:
    /// 1. Part of the value of `input`
    /// 2. The most-recently modified location for `src`
    fn find_data_inputs(
        &self,
        state: &PartialGraph<'tcx>,
        input: Place<'tcx>,
    ) -> Vec<DepNode<'tcx>> {
        // Include all sources of indirection (each reference in the chain) as relevant places.
        let provenance = input
            .refs_in_projection()
            .map(|(place_ref, _)| Place::from_ref(place_ref, self.tcx));
        let inputs = iter::once(input).chain(provenance);

        inputs
            // **POINTER-SENSITIVITY:**
            // If `input` involves indirection via dereferences, then resolve it to the direct places it could point to.
            .flat_map(|place| self.aliases(place))
            .flat_map(|alias| {
                // **FIELD-SENSITIVITY:**
                // Find all places that have been mutated which conflict with `alias.`
                let conflicts = state
                    .last_mutation
                    .iter()
                    .map(|(k, locs)| (*k, locs))
                    .filter(move |(place, _)| {
                        if place.is_indirect() && place.is_arg(&self.body) {
                            // HACK: `places_conflict` seems to consider it a bug is `borrow_place`
                            // includes a dereference, which should only happen if `borrow_place`
                            // is an argument. So we special case that condition and just compare for local equality.
                            //
                            // TODO: this is not field-sensitive!
                            place.local == alias.local
                        } else {
                            let mut place = *place;
                            if let Some((PlaceElem::Deref, rest)) = place.projection.split_last() {
                                let mut new_place = place;
                                new_place.projection = self.tcx.mk_place_elems(rest);
                                if new_place.ty(self.body.as_ref(), self.tcx).ty.is_box() {
                                    if new_place.is_indirect() {
                                        // TODO might be unsound: We assume that if
                                        // there are other indirections in here,
                                        // there is an alias that does not have
                                        // indirections in it.
                                        return false;
                                    }
                                    place = new_place;
                                }
                            }
                            places_conflict(
                                self.tcx,
                                &self.body,
                                place,
                                alias,
                                PlaceConflictBias::Overlap,
                            )
                        }
                    });

                // Special case: if the `alias` is an un-mutated argument, then include it as a conflict
                // coming from the special start location.
                let alias_last_mut = if alias.is_arg(&self.body) {
                    Some((alias, &self.start_loc))
                } else {
                    None
                };

                // For each `conflict`` last mutated at the locations `last_mut`:
                conflicts
                    .chain(alias_last_mut)
                    .flat_map(|(conflict, last_mut_locs)| {
                        // For each last mutated location:
                        last_mut_locs.iter().map(move |last_mut_loc| {
                            // Return <CONFLICT> @ <LAST_MUT_LOC> as an input node.
                            let at = self.make_call_string(*last_mut_loc);
                            DepNode::new(conflict, at, self.tcx, &self.body)
                        })
                    })
            })
            .collect()
    }

    /// Returns all nodes `dst` such that `dst` is an alias of `mutated`.
    ///
    /// Also updates the last-mutated location for `dst` to the given `location`.
    fn find_and_update_outputs(
        &self,
        state: &mut PartialGraph<'tcx>,
        mutated: Place<'tcx>,
        location: Location,
    ) -> Vec<DepNode<'tcx>> {
        // **POINTER-SENSITIVITY:**
        // If `mutated` involves indirection via dereferences, then resolve it to the direct places it could point to.
        let aliases = self.aliases(mutated).collect_vec();

        // **FIELD-SENSITIVITY:** we do NOT deal with fields on *writes* (in this function),
        // only on *reads* (in `add_input_to_op`).

        // For each mutated `dst`:
        aliases
            .iter()
            .map(|dst| {
                // Create a destination node for (DST @ CURRENT_LOC).
                let dst_node =
                    DepNode::new(*dst, self.make_call_string(location), self.tcx, &self.body);

                // Clear all previous mutations.
                let dst_mutations = state.last_mutation.entry(*dst).or_default();
                dst_mutations.clear();

                // Register that `dst` is mutated at the current location.
                dst_mutations.insert(RichLocation::Location(location));

                dst_node
            })
            .collect()
    }

    /// Update the PDG with arrows from `inputs` to `mutated` at `location`.
    fn apply_mutation(
        &self,
        state: &mut PartialGraph<'tcx>,
        location: Location,
        mutated: Either<Place<'tcx>, DepNode<'tcx>>,
        inputs: Inputs<'tcx>,
        target_use: TargetUse,
    ) {
        trace!("Applying mutation to {mutated:?} with inputs {inputs:?} at {location:?}");

        let ctrl_inputs = self.find_control_inputs(location);

        trace!("  Found control inputs {ctrl_inputs:?}");

        let data_inputs = match inputs {
            Inputs::Unresolved { places } => places
                .into_iter()
                .flat_map(|(input, input_use)| {
                    self.find_data_inputs(state, input)
                        .into_iter()
                        .map(move |input| {
                            (
                                input,
                                input_use.map_or(SourceUse::Operand, SourceUse::Argument),
                            )
                        })
                })
                .collect::<Vec<_>>(),
            Inputs::Resolved { node_use, node } => vec![(node, node_use)],
        };
        trace!("  Data inputs: {data_inputs:?}");

        let outputs = match mutated {
            Either::Left(place) => self.find_and_update_outputs(state, place, location),
            Either::Right(node) => vec![node],
        };
        trace!("  Outputs: {outputs:?}");

        for output in &outputs {
            trace!("  Adding node {output}");
            state.nodes.insert(*output);
        }

        // Add data dependencies: data_input -> output
        for (data_input, source_use) in data_inputs {
            let data_edge = DepEdge::data(self.make_call_string(location), source_use, target_use);
            for output in &outputs {
                trace!("  Adding edge {data_input} -> {output}");
                state.edges.insert((data_input, *output, data_edge));
            }
        }

        // Add control dependencies: ctrl_input -> output
        for (ctrl_input, edge) in &ctrl_inputs {
            for output in &outputs {
                state.edges.insert((*ctrl_input, *output, *edge));
            }
        }
    }

    /// Resolve a function [`Operand`] to a specific [`DefId`] and generic arguments if possible.
    pub(crate) fn operand_to_def_id(
        &self,
        func: &Operand<'tcx>,
    ) -> Option<(DefId, &'tcx List<GenericArg<'tcx>>)> {
        let ty = match func {
            Operand::Constant(func) => func.literal.ty(),
            Operand::Copy(place) | Operand::Move(place) => {
                place.ty(&self.body.local_decls, self.tcx).ty
            }
        };
        let ty = utils::ty_resolve(ty, self.tcx);
        match ty.kind() {
            TyKind::FnDef(def_id, generic_args) => Some((*def_id, generic_args)),
            TyKind::Generator(def_id, generic_args, _) => Some((*def_id, generic_args)),
            ty => {
                trace!("Bailing from handle_call because func is literal with type: {ty:?}");
                None
            }
        }
    }

    fn fmt_fn(&self, def_id: DefId) -> String {
        self.tcx.def_path_str(def_id)
    }

    /// Special case behavior for calls to functions used in desugaring async functions.
    ///
    /// Ensures that functions like `Pin::new_unchecked` are not modularly-approximated.
    fn approximate_async_functions(
        &self,
        state: &mut PartialGraph<'tcx>,
        def_id: DefId,
        args: &[Operand<'tcx>],
        destination: Place<'tcx>,
        location: Location,
    ) -> bool {
        let lang_items = self.tcx.lang_items();
        if Some(def_id) == lang_items.new_unchecked_fn() {
            let [op] = args else {
                unreachable!();
            };
            let mut operands = IndexVec::new();
            operands.push(op.clone());
            let TyKind::Adt(adt_id, generics) =
                destination.ty(self.body.as_ref(), self.tcx).ty.kind()
            else {
                unreachable!()
            };
            assert_eq!(adt_id.did(), lang_items.pin_type().unwrap());
            let aggregate_kind =
                AggregateKind::Adt(adt_id.did(), VariantIdx::from_u32(0), generics, None, None);
            let rvalue = Rvalue::Aggregate(Box::new(aggregate_kind), operands);
            trace!("Handling new_unchecked as assign for {destination:?}");
            self.modular_mutation_visitor(state)
                .visit_assign(&destination, &rvalue, location);
            true
        } else if Some(def_id) == lang_items.into_future_fn()
            // FIXME: better way to get retrieve this stdlib DefId?
            || self.tcx.def_path_str(def_id) == "<F as std::future::IntoFuture>::into_future"
        {
            trace!("Handling into_future as assign for {destination:?}");
            let [op] = args else {
                unreachable!();
            };
            self.modular_mutation_visitor(state).visit_assign(
                &destination,
                &Rvalue::Use(op.clone()),
                location,
            );
            true
        } else {
            false
        }
    }

    /// Attempt to inline a call to a function, returning None if call is not inline-able.
    fn handle_call(
        &self,
        state: &mut PartialGraph<'tcx>,
        location: Location,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        destination: Place<'tcx>,
    ) -> Option<()> {
        // Note: my comments here will use "child" to refer to the callee and
        // "parent" to refer to the caller, since the words are most visually distinct.

        let tcx = self.tcx;

        let (called_def_id, generic_args) = self.operand_to_def_id(func)?;
        trace!("Resolved call to function: {}", self.fmt_fn(called_def_id));

        // Monomorphize the called function with the known generic_args.
        let param_env = tcx.param_env_reveal_all_normalized(self.def_id);
        let resolved_fn =
            utils::try_resolve_function(self.tcx, called_def_id, param_env, generic_args);
        let resolved_def_id = resolved_fn.def_id();
        if log_enabled!(Level::Trace) && called_def_id != resolved_def_id {
            let (called, resolved) = (self.fmt_fn(called_def_id), self.fmt_fn(resolved_def_id));
            trace!("  `{called}` monomorphized to `{resolved}`",);
        }

        if is_non_default_trait_method(tcx, resolved_def_id).is_some() {
            trace!("  bailing because is unresolvable trait method");
            return None;
        }

        // Don't inline recursive calls.
        if let Some(cx) = &self.calling_context {
            if cx.call_stack.contains(&resolved_def_id) {
                trace!("  Bailing due to recursive call");
                return None;
            }
        }

        if self.approximate_async_functions(state, resolved_def_id, args, destination, location) {
            return Some(());
        }

        if !resolved_def_id.is_local() {
            trace!(
                "  Bailing because func is non-local: `{}`",
                tcx.def_path_str(resolved_def_id)
            );
            return None;
        };

        let call_kind = match self.classify_call_kind(called_def_id, resolved_def_id, args) {
            Ok(cc) => cc,
            Err(async_err) => {
                if let Some(cb) = self.params.call_change_callback.as_ref() {
                    cb.on_inline_miss(
                        resolved_fn,
                        location,
                        self.params.root,
                        self.calling_context.as_ref().map(|s| s.call_string),
                        InlineMissReason::Async(async_err),
                    )
                }
                return None;
            }
        };

        let calling_convention = CallingConvention::from_call_kind(&call_kind, args);

        trace!(
            "  Handling call! with kind {}",
            match &call_kind {
                CallKind::Direct => "direct",
                CallKind::Indirect => "indirect",
                CallKind::AsyncPoll { .. } => "async poll",
            }
        );

        // A helper to translate an argument (or return) in the child into a place in the parent.
        let parent_body = &self.body;
        let translate_to_parent = |child: Place<'tcx>| -> Option<Place<'tcx>> {
            trace!("  Translating child place: {child:?}");
            let (parent_place, child_projection) = calling_convention.handle_translate(
                &self.async_info,
                self.tcx,
                child,
                destination,
                &self.body,
            )?;

            let parent_place_projected = parent_place.project_deeper(child_projection, tcx);
            trace!("  ⮑ Translated to: {parent_place_projected:?}");
            Some(utils::retype_place(
                parent_place_projected,
                self.tcx,
                parent_body,
                self.def_id.to_def_id(),
            ))
        };

        // Recursively generate the PDG for the child function.
        let params = self.pdg_params_for_call(resolved_fn);
        let calling_context = self.calling_context_for(resolved_def_id, location);
        let call_string = calling_context.call_string;

        let cache_key = call_string.push(GlobalLocation {
            function: resolved_fn.def_id().expect_local(),
            location: RichLocation::Start,
        });

        let is_cached = self.pdg_cache.is_in_cache(&cache_key);

        let call_changes = self.params.call_change_callback.as_ref().map(|callback| {
            let info = CallInfo {
                callee: resolved_fn,
                call_string,
                is_cached,
                async_parent: if let CallKind::AsyncPoll(resolution, _loc, _) = call_kind {
                    // Special case for async. We ask for skipping not on the closure, but
                    // on the "async" function that created it. This is needed for
                    // consistency in skipping. Normally, when "poll" is inlined, mutations
                    // introduced by the creator of the future are not recorded and instead
                    // handled here, on the closure. But if the closure is skipped we need
                    // those mutations to occur. To ensure this we always ask for the
                    // "CallChanges" on the creator so that both creator and closure have
                    // the same view of whether they are inlined or "Skip"ped.
                    Some(resolution)
                } else {
                    None
                },
            };
            callback.on_inline(info)
        });

        // Handle async functions at the time of polling, not when the future is created.
        if tcx.asyncness(resolved_def_id).is_async() {
            trace!("  Bailing because func is async");

            // Register a synthetic assignment of `future = (arg0, arg1, ...)`.
            let rvalue = Rvalue::Aggregate(
                Box::new(AggregateKind::Tuple),
                IndexVec::from_iter(args.iter().cloned()),
            );
            self.modular_mutation_visitor(state)
                .visit_assign(&destination, &rvalue, location);

            // If a skip was requested then "poll" will not be inlined later so we
            // bail with "None" here and perform the mutations. Otherwise we bail with
            // "Some", knowing that handling "poll" later will handle the mutations.
            return (!matches!(
                &call_changes,
                Some(CallChanges {
                    skip: SkipCall::Skip,
                    ..
                })
            ))
            .then_some(());
        }

        if matches!(
            call_changes,
            Some(CallChanges {
                skip: SkipCall::Skip,
                ..
            })
        ) {
            trace!("  Bailing because user callback said to bail");
            return None;
        }

        let child_constructor = GraphConstructor::new(
            params,
            Some(calling_context),
            self.async_info.clone(),
            &self.pdg_cache,
        );

        if let Some(changes) = call_changes {
            for FakeEffect {
                place: callee_place,
                kind: cause,
            } in changes.fake_effects
            {
                let caller_place = match translate_to_parent(callee_place) {
                    Some(place) => place,
                    None => continue,
                };
                let source_use = Some(callee_place.local.as_u32() as u8);
                let target_use = TargetUse::Assign;
                let inputs = Inputs::Unresolved {
                    places: vec![(caller_place, source_use)],
                };
                match cause {
                    FakeEffectKind::Read => self.apply_mutation(
                        state,
                        location,
                        Either::Right(
                            child_constructor.make_dep_node(callee_place, RichLocation::Start),
                        ),
                        inputs,
                        target_use,
                    ),
                    FakeEffectKind::Write => self.apply_mutation(
                        state,
                        location,
                        Either::Left(caller_place),
                        inputs,
                        target_use,
                    ),
                };
            }
        }

        let child_graph = child_constructor.construct_partial_cached();

        // Find every reference to a parent-able node in the child's graph.
        let as_arg = |node: &DepNode<'tcx>| {
            if node.at.leaf().function != child_constructor.def_id {
                return None;
            }
            if node.place.local == RETURN_PLACE {
                Some(None)
            } else if node.place.is_arg(&child_constructor.body) {
                Some(Some(node.place.local.as_u32() as u8 - 1))
            } else {
                None
            }
        };
        let parentable_srcs = child_graph
            .edges
            .iter()
            .map(|(src, _, _)| *src)
            .filter_map(|a| Some((a, as_arg(&a)?)))
            .filter(|(node, _)| node.at.leaf().location.is_start());
        let parentable_dsts = child_graph
            .edges
            .iter()
            .map(|(_, dst, _)| *dst)
            .filter_map(|a| Some((a, as_arg(&a)?)))
            .filter(|node| node.0.at.leaf().location.is_end());

        // For each source node CHILD that is parentable to PLACE,
        // add an edge from PLACE -> CHILD.
        trace!("PARENT -> CHILD EDGES:");
        for (child_src, _kind) in parentable_srcs {
            if let Some(parent_place) = translate_to_parent(child_src.place) {
                self.apply_mutation(
                    state,
                    location,
                    Either::Right(child_src),
                    Inputs::Unresolved {
                        places: vec![(parent_place, None)],
                    },
                    TargetUse::Assign,
                );
            }
        }

        // For each destination node CHILD that is parentable to PLACE,
        // add an edge from CHILD -> PLACE.
        //
        // PRECISION TODO: for a given child place, we only want to connect
        // the *last* nodes in the child function to the parent, not *all* of them.
        trace!("CHILD -> PARENT EDGES:");
        for (child_dst, kind) in parentable_dsts {
            if let Some(parent_place) = translate_to_parent(child_dst.place) {
                self.apply_mutation(
                    state,
                    location,
                    Either::Left(parent_place),
                    Inputs::Resolved {
                        node: child_dst,
                        node_use: SourceUse::Operand,
                    },
                    kind.map_or(TargetUse::Return, TargetUse::MutArg),
                );
            }
        }

        state.nodes.extend(&child_graph.nodes);
        state.edges.extend(&child_graph.edges);

        trace!("  Inlined {}", self.fmt_fn(resolved_def_id));

        Some(())
    }

    fn modular_mutation_visitor<'a>(
        &'a self,
        state: &'a mut PartialGraph<'tcx>,
    ) -> ModularMutationVisitor<'a, 'tcx, impl FnMut(Location, Mutation<'tcx>) + 'a> {
        ModularMutationVisitor::new(&self.place_info, move |location, mutation| {
            self.apply_mutation(
                state,
                location,
                Either::Left(mutation.mutated),
                Inputs::Unresolved {
                    places: mutation.inputs,
                },
                mutation.mutation_reason,
            )
        })
    }

    fn handle_terminator(
        &self,
        terminator: &Terminator<'tcx>,
        state: &mut PartialGraph<'tcx>,
        location: Location,
    ) {
        match &terminator.kind {
            // Special case: if the current block is a SwitchInt, then other blocks could be control-dependent on it.
            // We need to create a node for the value of the discriminant at this point, so control-dependent mutations
            // can use it as a source.
            TerminatorKind::SwitchInt { discr, .. } => {
                if let Some(place) = discr.place() {
                    self.apply_mutation(
                        state,
                        location,
                        Either::Left(place),
                        Inputs::Unresolved {
                            places: vec![(place, None)],
                        },
                        TargetUse::Assign,
                    );
                }
            }

            // Special case: need to deal with context-sensitivity for function calls.
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                if self
                    .handle_call(state, location, func, args, *destination)
                    .is_none()
                {
                    self.modular_mutation_visitor(state)
                        .visit_terminator(terminator, location)
                }
            }

            // Fallback: call the visitor
            _ => self
                .modular_mutation_visitor(state)
                .visit_terminator(terminator, location),
        }
    }

    fn construct_partial_cached(&self) -> Rc<PartialGraph<'tcx>> {
        let key = self.make_call_string(RichLocation::Start);
        let pdg = self
            .pdg_cache
            .get(key, move |_| Rc::new(self.construct_partial()));
        Rc::clone(pdg)
    }

    pub(crate) fn construct_partial(&self) -> PartialGraph<'tcx> {
        if let Some(g) = self.try_handle_as_async() {
            return g;
        }

        let mut analysis = DfAnalysis(self)
            .into_engine(self.tcx, &self.body)
            .iterate_to_fixpoint()
            .into_results_cursor(&self.body);

        let mut final_state = PartialGraph::default();
        let all_returns = self.body.all_returns().map(|ret| ret.block).collect_vec();
        let has_return = !all_returns.is_empty();
        let blocks = if has_return {
            all_returns.clone()
        } else {
            self.body.basic_blocks.indices().collect_vec()
        };
        for block in blocks {
            analysis.seek_to_block_end(block);
            final_state.join(analysis.get());
        }

        if has_return {
            for block in all_returns {
                analysis.seek_to_block_end(block);
                let return_state = analysis.get();
                for (place, locations) in &return_state.last_mutation {
                    let ret_kind = if place.local == RETURN_PLACE {
                        TargetUse::Return
                    } else if let Some(num) = as_arg(*place, &self.body) {
                        TargetUse::MutArg(num)
                    } else {
                        continue;
                    };
                    for location in locations {
                        let src = self.make_dep_node(*place, *location);
                        let dst = self.make_dep_node(*place, RichLocation::End);
                        let edge = DepEdge::data(
                            self.make_call_string(self.body.terminator_loc(block)),
                            SourceUse::Operand,
                            ret_kind,
                        );
                        final_state.edges.insert((src, dst, edge));
                    }
                }
            }
        }

        final_state
    }

    fn domain_to_petgraph(self, domain: &PartialGraph<'tcx>) -> DepGraph<'tcx> {
        let mut graph: DiGraph<DepNode<'tcx>, DepEdge> = DiGraph::new();
        let mut nodes = FxHashMap::default();
        macro_rules! add_node {
            ($n:expr) => {
                *nodes.entry($n).or_insert_with(|| graph.add_node($n))
            };
        }

        for node in &domain.nodes {
            let _ = add_node!(*node);
        }

        for (src, dst, kind) in &domain.edges {
            let src_idx = add_node!(*src);
            let dst_idx = add_node!(*dst);
            graph.add_edge(src_idx, dst_idx, *kind);
        }

        DepGraph::new(graph)
    }

    pub fn construct(self) -> DepGraph<'tcx> {
        let partial = self.construct_partial_cached();
        self.domain_to_petgraph(&partial)
    }

    /// Determine the type of call-site.
    ///
    /// The error case is if we tried to resolve this as async and failed. We
    /// know it *is* async but we couldn't determine the information needed to
    /// analyze the function, therefore we will have to approximate it.
    fn classify_call_kind<'a>(
        &'a self,
        def_id: DefId,
        resolved_def_id: DefId,
        original_args: &'a [Operand<'tcx>],
    ) -> Result<CallKind<'tcx>, String> {
        match self.try_poll_call_kind(def_id, original_args) {
            AsyncDeterminationResult::Resolved(r) => Ok(r),
            AsyncDeterminationResult::NotAsync => Ok(self
                .try_indirect_call_kind(resolved_def_id)
                .unwrap_or(CallKind::Direct)),
            AsyncDeterminationResult::Unresolvable(reason) => Err(reason),
        }
    }

    fn try_indirect_call_kind(&self, def_id: DefId) -> Option<CallKind<'tcx>> {
        // let lang_items = self.tcx.lang_items();
        // let my_impl = self.tcx.impl_of_method(def_id)?;
        // let my_trait = self.tcx.trait_id_of_impl(my_impl)?;
        // (Some(my_trait) == lang_items.fn_trait()
        //     || Some(my_trait) == lang_items.fn_mut_trait()
        //     || Some(my_trait) == lang_items.fn_once_trait())
        // .then_some(CallKind::Indirect)
        self.tcx.is_closure(def_id).then_some(CallKind::Indirect)
    }
}

pub enum CallKind<'tcx> {
    /// A standard function call like `f(x)`.
    Direct,
    /// A call to a function variable, like `fn foo(f: impl Fn()) { f() }`
    Indirect,
    /// A poll to an async function, like `f.await`.
    AsyncPoll(FnResolution<'tcx>, Location, Place<'tcx>),
}

struct DfAnalysis<'a, 'tcx>(&'a GraphConstructor<'tcx>);

impl<'tcx> df::AnalysisDomain<'tcx> for DfAnalysis<'_, 'tcx> {
    type Domain = PartialGraph<'tcx>;

    const NAME: &'static str = "GraphConstructor";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        PartialGraph::default()
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, _state: &mut Self::Domain) {}
}

impl<'tcx> df::Analysis<'tcx> for DfAnalysis<'_, 'tcx> {
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.0
            .modular_mutation_visitor(state)
            .visit_statement(statement, location)
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.0.handle_terminator(terminator, state, location);
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: rustc_middle::mir::CallReturnPlaces<'_, 'tcx>,
    ) {
    }
}
