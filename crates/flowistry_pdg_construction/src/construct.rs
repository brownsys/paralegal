use std::{borrow::Cow, iter, rc::Rc};

use df::{fmt::DebugWithContext, Analysis, JoinSemiLattice};
use either::Either;
use flowistry_pdg::{CallString, GlobalLocation, RichLocation};
use itertools::Itertools;
use log::{debug, trace};
use petgraph::graph::DiGraph;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_borrowck::consumers::{places_conflict, BodyWithBorrowckFacts, PlaceConflictBias};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexSlice;
use rustc_middle::{
    mir::{
        visit::Visitor, AggregateKind, BasicBlock, Body, HasLocalDecls, Location, Operand, Place,
        PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorEdges, TerminatorKind,
        RETURN_PLACE,
    },
    ty::{GenericArg, GenericArgsRef, List, ParamEnv, TyCtxt, TyKind},
};
use rustc_mir_dataflow::{self as df};
use rustc_utils::cache::Cache;
use rustc_utils::{
    mir::{borrowck_facts, control_dependencies::ControlDependencies},
    BodyExt, PlaceExt,
};

use super::graph::{DepEdge, DepGraph, DepNode};
use super::utils::{self, FnResolution};
use flowistry::{
    infoflow::mutation::{ModularMutationVisitor, Mutation},
    mir::placeinfo::PlaceInfo,
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

    /// The call-stack up to the current call site.
    pub call_string: CallString,
}

type CallChangeCallback<'tcx> = Box<dyn Fn(CallInfo<'tcx>) -> CallChanges<'tcx> + 'tcx>;

/// Top-level parameters to PDG construction.
#[derive(Clone)]
pub struct PdgParams<'tcx> {
    tcx: TyCtxt<'tcx>,
    root: FnResolution<'tcx>,
    call_change_callback: Option<Rc<CallChangeCallback<'tcx>>>,
}

impl<'tcx> PdgParams<'tcx> {
    /// Must provide the [`TyCtxt`] and the [`LocalDefId`] of the function that is the root of the PDG.
    pub fn new(tcx: TyCtxt<'tcx>, root: LocalDefId) -> Self {
        PdgParams {
            tcx,
            root: FnResolution::Partial(root.to_def_id()),
            call_change_callback: None,
        }
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
    pub fn with_call_change_callback(
        self,
        f: impl Fn(CallInfo<'tcx>) -> CallChanges<'tcx> + 'tcx,
    ) -> Self {
        PdgParams {
            call_change_callback: Some(Rc::new(Box::new(f))),
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

struct CallingContext<'tcx> {
    call_string: CallString,
    param_env: ParamEnv<'tcx>,
    call_stack: Vec<DefId>,
}

/// Stores ids that are needed to construct projections around async functions.
struct AsyncInfo {
    poll_ready_variant_idx: VariantIdx,
    poll_ready_field_idx: FieldIdx,
}

impl AsyncInfo {
    fn make(tcx: TyCtxt) -> Option<Rc<Self>> {
        let lang_items = tcx.lang_items();
        let poll_def = tcx.adt_def(lang_items.poll()?);
        let ready_vid = lang_items.poll_ready_variant()?;
        assert_eq!(poll_def.variant_with_id(ready_vid).fields.len(), 1);
        Some(Rc::new(Self {
            poll_ready_variant_idx: poll_def.variant_index_with_id(ready_vid),
            poll_ready_field_idx: 0_u32.into(),
        }))
    }
}

type PdgCache<'tcx> = Rc<Cache<CallString, Rc<PartialGraph<'tcx>>>>;

pub struct GraphConstructor<'tcx> {
    tcx: TyCtxt<'tcx>,
    params: PdgParams<'tcx>,
    body_with_facts: &'tcx BodyWithBorrowckFacts<'tcx>,
    body: Cow<'tcx, Body<'tcx>>,
    def_id: LocalDefId,
    place_info: PlaceInfo<'tcx>,
    control_dependencies: ControlDependencies<BasicBlock>,
    body_assignments: utils::BodyAssignments,
    calling_context: Option<CallingContext<'tcx>>,
    start_loc: FxHashSet<RichLocation>,
    async_info: Rc<AsyncInfo>,
    pdg_cache: PdgCache<'tcx>,
}

macro_rules! let_assert {
  ($p:pat = $e:expr, $($arg:tt)*) => {
    let $p = $e else {
      panic!($($arg)*);
    };
  }
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
    fn new(
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
        let body = utils::try_monomorphize(tcx, params.root, param_env, &body_with_facts.body);

        if log::log_enabled!(log::Level::Debug) {
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
        match self.control_dependencies.dependent_on(location.block) {
            Some(ctrl_deps) => ctrl_deps
                .iter()
                .filter_map(|block| {
                    let ctrl_loc = self.body.terminator_loc(block);
                    let Terminator {
                        kind: TerminatorKind::SwitchInt { discr, .. },
                        ..
                    } = self.body.stmt_at(ctrl_loc).unwrap_right()
                    else {
                        return None;
                    };
                    let ctrl_place = discr.place()?;
                    let at = self.make_call_string(ctrl_loc);
                    let src = DepNode::new(ctrl_place, at, self.tcx, &self.body);
                    let edge = DepEdge::control(at);
                    Some((src, edge))
                })
                .collect_vec(),
            None => Vec::new(),
        }
    }

    /// Returns the aliases of `place`. See [`PlaceInfo::aliases`] for details.
    fn aliases(&self, place: Place<'tcx>) -> impl Iterator<Item = Place<'tcx>> + '_ {
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
                    .keys()
                    .filter(move |place| {
                        if place.is_indirect() && place.is_arg(&self.body) {
                            // HACK: `places_conflict` seems to consider it a bug is `borrow_place`
                            // includes a dereference, which should only happen if `borrow_place`
                            // is an argument. So we special case that condition and just compare for local equality.
                            //
                            // TODO: this is not field-sensitive!
                            place.local == alias.local
                        } else {
                            let mut place = **place;
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
                    })
                    .map(|place| (*place, &state.last_mutation[place]));

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
        inputs: Either<Vec<Place<'tcx>>, DepNode<'tcx>>,
    ) {
        trace!("Applying mutation to {mutated:?} with inputs {inputs:?}");

        let ctrl_inputs = self.find_control_inputs(location);

        let data_inputs = match inputs {
            Either::Left(places) => places
                .into_iter()
                .flat_map(|input| self.find_data_inputs(state, input))
                .collect::<Vec<_>>(),
            Either::Right(node) => vec![node],
        };
        trace!("  Data inputs: {data_inputs:?}");

        let outputs = match mutated {
            Either::Left(place) => self.find_and_update_outputs(state, place, location),
            Either::Right(node) => vec![node],
        };
        trace!("  Outputs: {outputs:?}");

        for output in &outputs {
            trace!("Adding node {output:?}");
            state.nodes.insert(*output);
        }

        // Add data dependencies: data_input -> output
        let data_edge = DepEdge::data(self.make_call_string(location));
        for data_input in data_inputs {
            for output in &outputs {
                trace!("Adding edge {data_input:?} -> {output:?}");
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

    /// Given the arguments to a `Future::poll` call, walk back through the
    /// body to find the original future being polled, and get the arguments to the future.
    fn find_async_args<'a>(
        &'a self,
        args: &'a [Operand<'tcx>],
    ) -> (
        FnResolution<'tcx>,
        Location,
        AsyncCallingConvention<'tcx, 'a>,
    ) {
        let get_def_for_op = |op: &Operand<'tcx>| -> Location {
            let_assert!(Some(place) = op.place(), "Arg is not a place");
            let_assert!(Some(local) = place.as_local(), "Place is not a local");
            let_assert!(
                Some(locs) = &self.body_assignments.get(&local),
                "Local has no assignments"
            );
            assert!(locs.len() == 1);
            locs[0]
        };

        let_assert!(
            Either::Right(Terminator {
                kind: TerminatorKind::Call {
                    args: new_pin_args,
                    ..
                },
                ..
            }) = &self.body.stmt_at(get_def_for_op(&args[0])),
            "Pinned assignment is not a call"
        );
        debug_assert!(new_pin_args.len() == 1);

        let future_aliases = self
            .aliases(self.tcx.mk_place_deref(new_pin_args[0].place().unwrap()))
            .collect_vec();
        debug_assert!(future_aliases.len() == 1);
        let future = *future_aliases.first().unwrap();

        let_assert!(
          Either::Left(Statement {
            kind: StatementKind::Assign(box (_, Rvalue::Use(future2))),
            ..
          }) = &self.body.stmt_at(get_def_for_op(&Operand::Move(future))),
          "Assignment to pin::new input is not a statement"
        );

        let_assert!(
            Either::Right(Terminator {
                kind: TerminatorKind::Call {
                    args: into_future_args,
                    ..
                },
                ..
            }) = &self.body.stmt_at(get_def_for_op(future2)),
            "Assignment to alias of pin::new input is not a call"
        );

        let mut chase_target = Err(&into_future_args[0]);

        while let Err(target) = chase_target {
            let async_fn_call_loc = get_def_for_op(target);
            let stmt = &self.body.stmt_at(async_fn_call_loc);
            chase_target = match stmt {
                Either::Right(Terminator {
                    kind: TerminatorKind::Call { args, func, .. },
                    ..
                }) => {
                    let (op, generics) = self.operand_to_def_id(func).unwrap();
                    Ok((
                        op,
                        generics,
                        AsyncCallingConvention::Fn(args),
                        async_fn_call_loc,
                    ))
                }
                Either::Left(Statement { kind, .. }) => match kind {
                    StatementKind::Assign(box (
                        _,
                        Rvalue::Aggregate(
                            box AggregateKind::Generator(def_id, generic_args, _),
                            args,
                        ),
                    )) => Ok((
                        *def_id,
                        *generic_args,
                        AsyncCallingConvention::Block(args),
                        async_fn_call_loc,
                    )),
                    StatementKind::Assign(box (_, Rvalue::Use(target))) => Err(target),
                    _ => {
                        panic!("Assignment to into_future input is not a call: {stmt:?}");
                    }
                },
                _ => {
                    panic!("Assignment to into_future input is not a call: {stmt:?}");
                }
            };
        }

        let (op, generics, calling_convention, async_fn_call_loc) = chase_target.unwrap();

        let resolution =
            utils::try_resolve_function(self.tcx, op, self.tcx.param_env(self.def_id), generics);

        (resolution, async_fn_call_loc, calling_convention)
    }

    /// Resolve a function [`Operand`] to a specific [`DefId`] and generic arguments if possible.
    fn operand_to_def_id(
        &self,
        func: &Operand<'tcx>,
    ) -> Option<(DefId, &'tcx List<GenericArg<'tcx>>)> {
        match func {
            Operand::Constant(func) => match func.literal.ty().kind() {
                TyKind::FnDef(def_id, generic_args) => Some((*def_id, generic_args)),
                ty => {
                    trace!("Bailing from handle_call because func is literal with type: {ty:?}");
                    None
                }
            },
            Operand::Copy(place) | Operand::Move(place) => {
                // TODO: control-flow analysis to deduce fn for inlined closures
                trace!("Bailing from handle_call because func is place {place:?}");
                None
            }
        }
    }

    fn fmt_fn(&self, def_id: DefId) -> String {
        self.tcx.def_path_str(def_id)
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
        let param_env = tcx.param_env(self.def_id);
        let resolved_fn =
            utils::try_resolve_function(self.tcx, called_def_id, param_env, generic_args);
        let resolved_def_id = resolved_fn.def_id();
        if called_def_id != resolved_def_id {
            let (called, resolved) = (self.fmt_fn(called_def_id), self.fmt_fn(resolved_def_id));
            trace!("  `{called}` monomorphized to `{resolved}`",);
        }

        // Don't inline recursive calls.
        if let Some(cx) = &self.calling_context {
            if cx.call_stack.contains(&resolved_def_id) {
                trace!("  Bailing due to recursive call");
                return None;
            }
        }

        if !resolved_def_id.is_local() {
            trace!(
                "  Bailing because func is non-local: `{}`",
                tcx.def_path_str(resolved_def_id)
            );
            return None;
        };

        let call_kind = self.classify_call_kind(called_def_id, args);

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
            trace!("    Translated to: {parent_place_projected:?}");
            Some(utils::retype_place(
                parent_place_projected,
                self.tcx,
                parent_body,
                self.def_id.to_def_id(),
            ))
        };

        let call_string = self.make_call_string(location);
        // Recursively generate the PDG for the child function.
        let params = PdgParams {
            root: resolved_fn,
            ..self.params.clone()
        };
        let call_stack = match &self.calling_context {
            Some(cx) => {
                let mut stack = cx.call_stack.clone();
                stack.push(resolved_def_id);
                stack
            }
            None => vec![resolved_def_id],
        };
        let calling_context = CallingContext {
            call_string,
            param_env,
            call_stack,
        };

        let call_changes = self.params.call_change_callback.as_ref().map(|callback| {
            let info = if let CallKind::AsyncPoll(resolution, loc, _) = call_kind {
                // Special case for async. We ask for skipping not on the closure, but
                // on the "async" function that created it. This is needed for
                // consistency in skipping. Normally, when "poll" is inlined, mutations
                // introduced by the creator of the future are not recorded and instead
                // handled here, on the closure. But if the closure is skipped we need
                // those mutations to occur. To ensure this we always ask for the
                // "CallChanges" on the creator so that both creator and closure have
                // the same view of whether they are inlined or "Skip"ped.
                CallInfo {
                    callee: resolution,
                    call_string: self.make_call_string(loc),
                }
            } else {
                CallInfo {
                    callee: resolved_fn,
                    call_string,
                }
            };
            callback(info)
        });

        // Handle async functions at the time of polling, not when the future is created.
        if tcx.asyncness(resolved_def_id).is_async() {
            trace!("  Bailing because func is async");
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
                match cause {
                    FakeEffectKind::Read => self.apply_mutation(
                        state,
                        location,
                        Either::Right(
                            child_constructor.make_dep_node(callee_place, RichLocation::Start),
                        ),
                        Either::Left(vec![caller_place]),
                    ),
                    FakeEffectKind::Write => self.apply_mutation(
                        state,
                        location,
                        Either::Left(caller_place),
                        Either::Left(vec![caller_place]),
                    ),
                };
            }
        }

        let child_graph = child_constructor.construct_partial_cached();

        // Find every reference to a parent-able node in the child's graph.
        let is_arg = |node: &DepNode<'tcx>| {
            node.at.leaf().function == child_constructor.def_id
                && (node.place.local == RETURN_PLACE || node.place.is_arg(&child_constructor.body))
        };
        let parentable_srcs = child_graph
            .edges
            .iter()
            .map(|(src, _, _)| *src)
            .filter(is_arg)
            .filter(|node| node.at.leaf().location.is_start());
        let parentable_dsts = child_graph
            .edges
            .iter()
            .map(|(_, dst, _)| *dst)
            .filter(is_arg)
            .filter(|node| node.at.leaf().location.is_end());

        // For each source node CHILD that is parentable to PLACE,
        // add an edge from PLACE -> CHILD.
        for child_src in parentable_srcs {
            if let Some(parent_place) = translate_to_parent(child_src.place) {
                self.apply_mutation(
                    state,
                    location,
                    Either::Right(child_src),
                    Either::Left(vec![parent_place]),
                );
            }
        }

        // For each destination node CHILD that is parentable to PLACE,
        // add an edge from CHILD -> PLACE.
        //
        // PRECISION TODO: for a given child place, we only want to connect
        // the *last* nodes in the child function to the parent, not *all* of them.
        for child_dst in parentable_dsts {
            if let Some(parent_place) = translate_to_parent(child_dst.place) {
                self.apply_mutation(
                    state,
                    location,
                    Either::Left(parent_place),
                    Either::Right(child_dst),
                );
            }
        }

        state.nodes.extend(&child_graph.nodes);
        state.edges.extend(&child_graph.edges);

        trace!("  Inlined {}", self.fmt_fn(resolved_def_id));

        Some(())
    }

    fn async_generator(body: &Body<'tcx>) -> (LocalDefId, GenericArgsRef<'tcx>, Location) {
        let block = BasicBlock::from_usize(0);
        let location = Location {
            block,
            statement_index: body.basic_blocks[block].statements.len() - 1,
        };
        let stmt = body
            .stmt_at(location)
            .expect_left("Async fn should have a statement");
        let StatementKind::Assign(box (
            _,
            Rvalue::Aggregate(box AggregateKind::Generator(def_id, generic_args, _), _args),
        )) = &stmt.kind
        else {
            panic!("Async fn should assign to a generator")
        };
        (def_id.expect_local(), generic_args, location)
    }

    fn modular_mutation_visitor<'a>(
        &'a self,
        state: &'a mut PartialGraph<'tcx>,
    ) -> ModularMutationVisitor<'a, 'tcx, impl FnMut(Location, Vec<Mutation<'tcx>>) + 'a> {
        ModularMutationVisitor::new(&self.place_info, |location, mutations| {
            for mutation in mutations {
                self.apply_mutation(
                    state,
                    location,
                    Either::Left(mutation.mutated),
                    Either::Left(mutation.inputs),
                );
            }
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
                        Either::Left(vec![place]),
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

    fn determine_async(&self) -> Option<(LocalDefId, GenericArgsRef<'tcx>, Location)> {
        if self.tcx.asyncness(self.def_id).is_async() {
            Some(Self::async_generator(&self.body))
        } else {
            try_as_async_trait_function(self.tcx, self.def_id.to_def_id(), self.body.as_ref())
        }
    }

    fn construct_partial_cached(&self) -> Rc<PartialGraph<'tcx>> {
        let key = self.make_call_string(RichLocation::Start);
        let pdg = self
            .pdg_cache
            .get(key, move |_| Rc::new(self.construct_partial()));
        Rc::clone(pdg)
    }

    fn construct_partial(&self) -> PartialGraph<'tcx> {
        if let Some((generator_def_id, generic_args, location)) = self.determine_async() {
            let param_env = self.tcx.param_env(self.def_id);
            let generator_fn = utils::try_resolve_function(
                self.tcx,
                generator_def_id.to_def_id(),
                param_env,
                generic_args,
            );
            let params = PdgParams {
                root: generator_fn,
                ..self.params.clone()
            };
            let call_string = self.make_call_string(location);
            let call_stack = match &self.calling_context {
                Some(cx) => cx.call_stack.clone(),
                None => vec![],
            };
            let calling_context = CallingContext {
                param_env,
                call_string,
                call_stack,
            };
            return GraphConstructor::new(
                params,
                Some(calling_context),
                self.async_info.clone(),
                &self.pdg_cache,
            )
            .construct_partial();
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
                    if place.local == RETURN_PLACE || place.is_arg(&self.body) {
                        for location in locations {
                            let src = self.make_dep_node(*place, *location);
                            let dst = self.make_dep_node(*place, RichLocation::End);
                            let edge = DepEdge::data(
                                self.make_call_string(self.body.terminator_loc(block)),
                            );
                            final_state.edges.insert((src, dst, edge));
                        }
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
    fn classify_call_kind<'a>(
        &'a self,
        def_id: DefId,
        original_args: &'a [Operand<'tcx>],
    ) -> CallKind<'tcx, 'a> {
        self.try_poll_call_kind(def_id, original_args)
            .or_else(|| self.try_indirect_call_kind(def_id))
            .unwrap_or(CallKind::Direct)
    }

    fn try_indirect_call_kind(&self, def_id: DefId) -> Option<CallKind<'tcx, '_>> {
        let lang_items = self.tcx.lang_items();
        let my_impl = self.tcx.impl_of_method(def_id)?;
        let my_trait = self.tcx.trait_id_of_impl(my_impl)?;
        (Some(my_trait) == lang_items.fn_trait()
            || Some(my_trait) == lang_items.fn_mut_trait()
            || Some(my_trait) == lang_items.fn_once_trait())
        .then_some(CallKind::Indirect)
    }

    fn try_poll_call_kind<'a>(
        &'a self,
        def_id: DefId,
        original_args: &'a [Operand<'tcx>],
    ) -> Option<CallKind<'tcx, 'a>> {
        let lang_items = self.tcx.lang_items();
        if lang_items.future_poll_fn() == Some(def_id) {
            let (fun, loc, args) = self.find_async_args(original_args);
            Some(CallKind::AsyncPoll(fun, loc, args))
        } else {
            None
        }
    }
}

fn has_async_trait_signature(tcx: TyCtxt, def_id: DefId) -> bool {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        let sig = tcx.fn_sig(def_id).skip_binder();
        assoc_item.container == ty::AssocItemContainer::ImplContainer
            && assoc_item.trait_item_def_id.is_some()
            && match_pin_box_dyn_ty(tcx.lang_items(), sig.output().skip_binder())
    } else {
        false
    }
}

fn try_as_async_trait_function<'tcx>(
    tcx: TyCtxt,
    def_id: DefId,
    body: &Body<'tcx>,
) -> Option<(LocalDefId, GenericArgsRef<'tcx>, Location)> {
    if !has_async_trait_signature(tcx, def_id) {
        return None;
    }
    let mut matching_statements =
        body.basic_blocks
            .iter_enumerated()
            .flat_map(|(block, bbdat)| {
                bbdat.statements.iter().enumerate().filter_map(
                    move |(statement_index, statement)| {
                        let StatementKind::Assign(box (
                            _,
                            Rvalue::Aggregate(
                                box AggregateKind::Generator(def_id, generic_args, _),
                                _args,
                            ),
                        )) = &statement.kind
                        else {
                            return None;
                        };
                        Some((
                            def_id.as_local()?,
                            *generic_args,
                            Location {
                                block,
                                statement_index,
                            },
                        ))
                    },
                )
            })
            .collect::<Vec<_>>();
    assert_eq!(matching_statements.len(), 1);
    matching_statements.pop()
}

/// Does this fucntion have a structure as created by the `#[async_trait]` macro
pub fn is_async_trait_fn(tcx: TyCtxt, def_id: DefId, body: &Body<'_>) -> bool {
    try_as_async_trait_function(tcx, def_id, body).is_some()
}

use rustc_middle::ty;
fn match_pin_box_dyn_ty(lang_items: &rustc_hir::LanguageItems, t: ty::Ty) -> bool {
    let ty::TyKind::Adt(pin_ty, args) = t.kind() else {
        return false;
    };
    if Some(pin_ty.did()) != lang_items.pin_type() {
        return false;
    };
    let [arg] = args.as_slice() else { return false };
    let Some(t_a) = arg.as_type() else {
        return false;
    };
    if !t_a.is_box() {
        return false;
    };
    let ty::TyKind::Dynamic(pred, _, ty::DynKind::Dyn) = t_a.boxed_ty().kind() else {
        return false;
    };
    if pred.len() != 2 {
        return false;
    }
    pred.iter().any(|p| {
        let ty::ExistentialPredicate::Trait(t) = p.skip_binder() else {
            return false;
        };
        Some(t.def_id) == lang_items.future_trait()
    })
}

enum CallKind<'tcx, 'a> {
    /// A standard function call like `f(x)`.
    Direct,
    /// A call to a function variable, like `fn foo(f: impl Fn()) { f() }`
    Indirect,
    /// A poll to an async function, like `f.await`.
    AsyncPoll(
        FnResolution<'tcx>,
        Location,
        AsyncCallingConvention<'tcx, 'a>,
    ),
}

enum CallingConvention<'tcx, 'a> {
    Direct(&'a [Operand<'tcx>]),
    Indirect {
        closure_arg: &'a Operand<'tcx>,
        tupled_arguments: &'a Operand<'tcx>,
    },
    Async(AsyncCallingConvention<'tcx, 'a>),
}

impl<'tcx, 'a> CallingConvention<'tcx, 'a> {
    fn from_call_kind(
        kind: &CallKind<'tcx, 'a>,
        args: &'a [Operand<'tcx>],
    ) -> CallingConvention<'tcx, 'a> {
        match kind {
            CallKind::AsyncPoll(_, _, args) => CallingConvention::Async(*args),
            CallKind::Direct => CallingConvention::Direct(args),
            CallKind::Indirect => CallingConvention::Indirect {
                closure_arg: &args[0],
                tupled_arguments: &args[1],
            },
        }
    }

    fn handle_translate(
        &self,
        async_info: &AsyncInfo,
        tcx: TyCtxt<'tcx>,
        child: Place<'tcx>,
        destination: Place<'tcx>,
        parent_body: &Body<'tcx>,
    ) -> Option<(Place<'tcx>, &[PlaceElem<'tcx>])> {
        let result = match self {
            // Async return must be handled special, because it gets wrapped in `Poll::Ready`
            Self::Async { .. } if child.local == RETURN_PLACE => {
                let in_poll = destination.project_deeper(
                    &[PlaceElem::Downcast(None, async_info.poll_ready_variant_idx)],
                    tcx,
                );
                let field_idx = async_info.poll_ready_field_idx;
                let child_inner_return_type = in_poll
                    .ty(parent_body.local_decls(), tcx)
                    .field_ty(tcx, field_idx);
                (
                    in_poll.project_deeper(
                        &[PlaceElem::Field(field_idx, child_inner_return_type)],
                        tcx,
                    ),
                    &child.projection[..],
                )
            }
            _ if child.local == RETURN_PLACE => (destination, &child.projection[..]),
            // Map arguments to the argument array
            Self::Direct(args) => (
                args[child.local.as_usize() - 1].place()?,
                &child.projection[..],
            ),
            // Map arguments to projections of the future, the poll's first argument
            Self::Async(cc) => {
                if child.local.as_usize() == 1 {
                    let PlaceElem::Field(idx, _) = child.projection[0] else {
                        panic!("Unexpected non-projection of async context")
                    };
                    let op = match cc {
                        AsyncCallingConvention::Fn(args) => &args[idx.as_usize()],
                        AsyncCallingConvention::Block(args) => &args[idx],
                    };
                    (op.place()?, &child.projection[1..])
                } else {
                    return None;
                }
            }
            // Map closure captures to the first argument.
            // Map formal parameters to the second argument.
            Self::Indirect {
                closure_arg,
                tupled_arguments,
            } => {
                if child.local.as_usize() == 1 {
                    (closure_arg.place()?, &child.projection[..])
                } else {
                    let tuple_arg = tupled_arguments.place()?;
                    let _projection = child.projection.to_vec();
                    let field = FieldIdx::from_usize(child.local.as_usize() - 2);
                    let field_ty = tuple_arg.ty(parent_body, tcx).field_ty(tcx, field);
                    (
                        tuple_arg.project_deeper(&[PlaceElem::Field(field, field_ty)], tcx),
                        &child.projection[..],
                    )
                }
            }
        };
        Some(result)
    }
}

#[derive(Clone, Copy)]
enum AsyncCallingConvention<'tcx, 'a> {
    Fn(&'a [Operand<'tcx>]),
    Block(&'a IndexSlice<FieldIdx, Operand<'tcx>>),
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
