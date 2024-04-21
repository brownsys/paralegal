use std::{borrow::Cow, collections::HashSet, iter, rc::Rc};

use df::{fmt::DebugWithContext, Analysis, AnalysisDomain, Results, ResultsVisitor};
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
    mutation::Time,
    utils::{is_non_default_trait_method, manufacture_substs_for},
    InlineMissReason, SkipCall,
};
use crate::{
    mutation::{ModularMutationVisitor, Mutation},
    try_resolve_function, CallChangeCallback, CallChanges, CallInfo,
};

/// Top-level parameters to PDG construction.
#[derive(Clone)]
pub struct PdgParams<'tcx> {
    tcx: TyCtxt<'tcx>,
    root: FnResolution<'tcx>,
    call_change_callback: Option<Rc<dyn CallChangeCallback<'tcx> + 'tcx>>,
    dump_mir: bool,
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
pub struct InstructionState<'tcx> {
    last_mutation: FxHashMap<Place<'tcx>, FxHashSet<RichLocation>>,
}

impl<C> DebugWithContext<C> for InstructionState<'_> {}

impl<'tcx> df::JoinSemiLattice for InstructionState<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let b3 = utils::hashmap_join(
            &mut self.last_mutation,
            &other.last_mutation,
            utils::hashset_join,
        );
        b3
    }
}

#[derive(Default, Debug)]
pub struct PartialGraph<'tcx> {
    nodes: FxHashSet<DepNode<'tcx>>,
    edges: FxHashSet<(DepNode<'tcx>, DepNode<'tcx>, DepEdge)>,
}

impl<'mir, 'tcx> ResultsVisitor<'mir, 'tcx, Results<'tcx, DfAnalysis<'mir, 'tcx>>>
    for PartialGraph<'tcx>
{
    type FlowState = <DfAnalysis<'mir, 'tcx> as AnalysisDomain<'tcx>>::Domain;

    fn visit_statement_before_primary_effect(
        &mut self,
        results: &Results<'tcx, DfAnalysis<'mir, 'tcx>>,
        state: &Self::FlowState,
        statement: &'mir rustc_middle::mir::Statement<'tcx>,
        location: Location,
    ) {
        let mut vis = self.modular_mutation_visitor(results, state);

        vis.visit_statement(statement, location)
    }

    /// We handle terminators during graph construction generally in the before
    /// state, because we're interested in what the dependencies of our read
    /// places are before the modification pass overwrites the read places from
    /// any mutable arguments.
    ///
    /// There is one exception which is that non-inlined function calls are
    /// handled in two steps. Before the primary effects we generate edges from
    /// the dependencies to the input arguments. After the primary effect we
    /// insert edges from each argument to each modified location. It is cleaner
    /// to do this afterwards, because the logic that resolves a place to a
    /// graph node assumes that you are reading all of your inputs from the
    /// "last_modification". In the "before" state that map contains the
    /// "original" dependencies of each argument, e.g. we haven't combined them
    /// with the reachable places yet. So this ordering means we can reuse the
    /// same logic but just have to run it twice for every non-inlined function
    /// call site.
    fn visit_terminator_before_primary_effect(
        &mut self,
        results: &Results<'tcx, DfAnalysis<'mir, 'tcx>>,
        state: &Self::FlowState,
        terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
        let mut handle_as_inline = || {
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
            else {
                return None;
            };
            let constructor = results.analysis.0;

            let (child_constructor, calling_convention) =
                match constructor.determine_call_handling(location, func, args)? {
                    CallHandling::Ready(one, two) => (one, two),
                    CallHandling::ApproxAsyncFn => {
                        // Register a synthetic assignment of `future = (arg0, arg1, ...)`.
                        let rvalue = Rvalue::Aggregate(
                            Box::new(AggregateKind::Tuple),
                            IndexVec::from_iter(args.iter().cloned()),
                        );
                        self.modular_mutation_visitor(results, state).visit_assign(
                            &destination,
                            &rvalue,
                            location,
                        );
                        return Some(());
                    }
                    CallHandling::ApproxAsyncSM(how) => {
                        how(
                            constructor,
                            &mut self.modular_mutation_visitor(results, state),
                            &args,
                            *destination,
                            location,
                        );
                        return Some(());
                    }
                };

            let child_graph = child_constructor.construct_partial_cached();

            let parentable_srcs =
                child_graph.parentable_srcs(child_constructor.def_id, &child_constructor.body);
            let parentable_dsts =
                child_graph.parentable_dsts(child_constructor.def_id, &child_constructor.body);

            // For each source node CHILD that is parentable to PLACE,
            // add an edge from PLACE -> CHILD.
            trace!("PARENT -> CHILD EDGES:");
            for (child_src, _kind) in parentable_srcs {
                if let Some(parent_place) = calling_convention.translate_to_parent(
                    child_src.place,
                    &constructor.async_info,
                    constructor.tcx,
                    &constructor.body,
                    constructor.def_id.to_def_id(),
                    *destination,
                ) {
                    self.register_mutation(
                        results,
                        state,
                        Inputs::Unresolved {
                            places: vec![(parent_place, None)],
                        },
                        Either::Right(child_src),
                        location,
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
                if let Some(parent_place) = calling_convention.translate_to_parent(
                    child_dst.place,
                    &constructor.async_info,
                    constructor.tcx,
                    &constructor.body,
                    constructor.def_id.to_def_id(),
                    *destination,
                ) {
                    self.register_mutation(
                        results,
                        state,
                        Inputs::Resolved {
                            node: child_dst,
                            node_use: SourceUse::Operand,
                        },
                        Either::Left(parent_place),
                        location,
                        kind.map_or(TargetUse::Return, TargetUse::MutArg),
                    );
                }
            }
            self.nodes.extend(&child_graph.nodes);
            self.edges.extend(&child_graph.edges);
            Some(())
        };

        if let TerminatorKind::SwitchInt { discr, .. } = &terminator.kind {
            if let Some(place) = discr.place() {
                self.register_mutation(
                    results,
                    state,
                    Inputs::Unresolved {
                        places: vec![(place, None)],
                    },
                    Either::Left(place),
                    location,
                    TargetUse::Assign,
                );
            }
            return;
        }

        if handle_as_inline().is_none() {
            trace!("Handling terminator {:?} as not inlined", terminator.kind);
            let mut arg_vis = ModularMutationVisitor::new(
                &results.analysis.0.place_info,
                move |location, mutation| {
                    self.register_mutation(
                        results,
                        state,
                        Inputs::Unresolved {
                            places: mutation.inputs,
                        },
                        Either::Left(mutation.mutated),
                        location,
                        mutation.mutation_reason,
                    )
                },
            );
            arg_vis.set_time(Time::Before);
            arg_vis.visit_terminator(terminator, location);
        }
    }

    fn visit_terminator_after_primary_effect(
        &mut self,
        results: &Results<'tcx, DfAnalysis<'mir, 'tcx>>,
        state: &Self::FlowState,
        terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
            let constructor = results.analysis.0;

            if matches!(
                constructor.determine_call_handling(location, func, args),
                Some(CallHandling::Ready(_, _))
            ) {
                return;
            }
        }

        trace!("Handling terminator {:?} as not inlined", terminator.kind);
        let mut arg_vis = ModularMutationVisitor::new(
            &results.analysis.0.place_info,
            move |location, mutation| {
                self.register_mutation(
                    results,
                    state,
                    Inputs::Unresolved {
                        places: mutation.inputs,
                    },
                    Either::Left(mutation.mutated),
                    location,
                    mutation.mutation_reason,
                )
            },
        );
        arg_vis.set_time(Time::After);
        arg_vis.visit_terminator(terminator, location);
    }
}
fn as_arg<'tcx>(node: &DepNode<'tcx>, def_id: LocalDefId, body: &Body<'tcx>) -> Option<Option<u8>> {
    if node.at.leaf().function != def_id {
        return None;
    }
    if node.place.local == RETURN_PLACE {
        Some(None)
    } else if node.place.is_arg(&body) {
        Some(Some(node.place.local.as_u32() as u8 - 1))
    } else {
        None
    }
}

impl<'tcx> PartialGraph<'tcx> {
    fn modular_mutation_visitor<'a>(
        &'a mut self,
        results: &'a Results<'tcx, DfAnalysis<'_, 'tcx>>,
        state: &'a InstructionState<'tcx>,
    ) -> ModularMutationVisitor<'a, 'tcx, impl FnMut(Location, Mutation<'tcx>) + 'a> {
        ModularMutationVisitor::new(&results.analysis.0.place_info, move |location, mutation| {
            self.register_mutation(
                results,
                state,
                Inputs::Unresolved {
                    places: mutation.inputs,
                },
                Either::Left(mutation.mutated),
                location,
                mutation.mutation_reason,
            )
        })
    }
    fn parentable_srcs<'a>(
        &'a self,
        def_id: LocalDefId,
        body: &'a Body<'tcx>,
    ) -> impl Iterator<Item = (DepNode<'tcx>, Option<u8>)> + 'a {
        self.edges
            .iter()
            .map(|(src, _, _)| *src)
            .filter_map(move |a| Some((a, as_arg(&a, def_id, body)?)))
            .filter(|(node, _)| node.at.leaf().location.is_start())
    }

    fn parentable_dsts<'a>(
        &'a self,
        def_id: LocalDefId,
        body: &'a Body<'tcx>,
    ) -> impl Iterator<Item = (DepNode<'tcx>, Option<u8>)> + 'a {
        self.edges
            .iter()
            .map(|(_, dst, _)| *dst)
            .filter_map(move |a| Some((a, as_arg(&a, def_id, body)?)))
            .filter(|node| node.0.at.leaf().location.is_end())
    }

    fn register_mutation(
        &mut self,
        results: &Results<'tcx, DfAnalysis<'_, 'tcx>>,
        state: &InstructionState<'tcx>,
        inputs: Inputs<'tcx>,
        mutated: Either<Place<'tcx>, DepNode<'tcx>>,
        location: Location,
        target_use: TargetUse,
    ) {
        trace!("Registering mutation to {mutated:?} with inputs {inputs:?} at {location:?}");
        let constructor = results.analysis.0;
        let ctrl_inputs = constructor.find_control_inputs(location);

        trace!("  Found control inputs {ctrl_inputs:?}");

        let data_inputs = match inputs {
            Inputs::Unresolved { places } => places
                .into_iter()
                .flat_map(|(input, input_use)| {
                    constructor
                        .find_data_inputs(state, input)
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
            Either::Right(node) => vec![node],
            Either::Left(place) => results
                .analysis
                .0
                .find_outputs(state, place, location)
                .into_iter()
                .map(|t| t.1)
                .collect(),
        };
        trace!("  Outputs: {outputs:?}");

        for output in &outputs {
            trace!("  Adding node {output}");
            self.nodes.insert(*output);
        }

        // Add data dependencies: data_input -> output
        for (data_input, source_use) in data_inputs {
            let data_edge = DepEdge::data(
                constructor.make_call_string(location),
                source_use,
                target_use,
            );
            for output in &outputs {
                trace!("  Adding edge {data_input} -> {output}");
                self.edges.insert((data_input, *output, data_edge));
            }
        }

        // Add control dependencies: ctrl_input -> output
        for (ctrl_input, edge) in &ctrl_inputs {
            for output in &outputs {
                self.edges.insert((*ctrl_input, *output, *edge));
            }
        }
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

fn other_as_arg<'tcx>(place: Place<'tcx>, body: &Body<'tcx>) -> Option<u8> {
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

        if params.dump_mir || log_enabled!(log::Level::Trace) {
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
        state: &InstructionState<'tcx>,
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

    fn find_outputs(
        &self,
        _state: &InstructionState<'tcx>,
        mutated: Place<'tcx>,
        location: Location,
    ) -> Vec<(Place<'tcx>, DepNode<'tcx>)> {
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
                (
                    *dst,
                    DepNode::new(*dst, self.make_call_string(location), self.tcx, &self.body),
                )
            })
            .collect()
    }

    /// Updates the last-mutated location for `dst` to the given `location`.
    fn apply_mutation(
        &self,
        state: &mut InstructionState<'tcx>,
        location: Location,
        mutated: Place<'tcx>,
    ) {
        self.find_outputs(state, mutated, location)
            .into_iter()
            .for_each(|(dst, _)| {
                // Create a destination node for (DST @ CURRENT_LOC).

                // Clear all previous mutations.
                let dst_mutations = state.last_mutation.entry(dst).or_default();
                dst_mutations.clear();

                // Register that `dst` is mutated at the current location.
                dst_mutations.insert(RichLocation::Location(location));
            })
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
    fn can_approximate_async_functions(
        &self,
        def_id: DefId,
    ) -> Option<fn(&Self, &mut dyn Visitor<'tcx>, &[Operand<'tcx>], Place<'tcx>, Location)> {
        let lang_items = self.tcx.lang_items();
        if Some(def_id) == lang_items.new_unchecked_fn() {
            Some(Self::approximate_new_unchecked)
        } else if Some(def_id) == lang_items.into_future_fn()
            // FIXME: better way to get retrieve this stdlib DefId?
            || self.tcx.def_path_str(def_id) == "<F as std::future::IntoFuture>::into_future"
        {
            Some(Self::approximate_into_future)
        } else {
            None
        }
    }

    fn approximate_into_future(
        &self,
        vis: &mut dyn Visitor<'tcx>,
        args: &[Operand<'tcx>],
        destination: Place<'tcx>,
        location: Location,
    ) {
        trace!("Handling into_future as assign for {destination:?}");
        let [op] = args else {
            unreachable!();
        };
        vis.visit_assign(&destination, &Rvalue::Use(op.clone()), location);
    }

    fn approximate_new_unchecked(
        &self,
        vis: &mut dyn Visitor<'tcx>,
        args: &[Operand<'tcx>],
        destination: Place<'tcx>,
        location: Location,
    ) {
        let lang_items = self.tcx.lang_items();
        let [op] = args else {
            unreachable!();
        };
        let mut operands = IndexVec::new();
        operands.push(op.clone());
        let TyKind::Adt(adt_id, generics) = destination.ty(self.body.as_ref(), self.tcx).ty.kind()
        else {
            unreachable!()
        };
        assert_eq!(adt_id.did(), lang_items.pin_type().unwrap());
        let aggregate_kind =
            AggregateKind::Adt(adt_id.did(), VariantIdx::from_u32(0), generics, None, None);
        let rvalue = Rvalue::Aggregate(Box::new(aggregate_kind), operands);
        trace!("Handling new_unchecked as assign for {destination:?}");
        vis.visit_assign(&destination, &rvalue, location);
    }

    fn determine_call_handling<'a>(
        &self,
        location: Location,
        func: &Operand<'tcx>,
        args: &'a [Operand<'tcx>],
    ) -> Option<CallHandling<'tcx, 'a>> {
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

        if let Some(handler) = self.can_approximate_async_functions(resolved_def_id) {
            return Some(CallHandling::ApproxAsyncSM(handler));
        };

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
            .then_some(CallHandling::ApproxAsyncFn);
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
        Some(CallHandling::Ready(child_constructor, calling_convention))
    }

    /// Attempt to inline a call to a function, returning None if call is not inline-able.
    fn handle_call(
        &self,
        state: &mut InstructionState<'tcx>,
        location: Location,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        destination: Place<'tcx>,
    ) -> Option<()> {
        // Note: my comments here will use "child" to refer to the callee and
        // "parent" to refer to the caller, since the words are most visually distinct.

        let preamble = self.determine_call_handling(location, func, args)?;

        let (child_constructor, calling_convention) = match preamble {
            CallHandling::Ready(child_constructor, calling_convention) => {
                (child_constructor, calling_convention)
            }
            CallHandling::ApproxAsyncFn => {
                // Register a synthetic assignment of `future = (arg0, arg1, ...)`.
                let rvalue = Rvalue::Aggregate(
                    Box::new(AggregateKind::Tuple),
                    IndexVec::from_iter(args.iter().cloned()),
                );
                self.modular_mutation_visitor(state)
                    .visit_assign(&destination, &rvalue, location);
                return Some(());
            }
            CallHandling::ApproxAsyncSM(handler) => {
                handler(
                    self,
                    &mut self.modular_mutation_visitor(state),
                    args,
                    destination,
                    location,
                );
                return Some(());
            }
        };

        let child_graph = child_constructor.construct_partial_cached();

        let parentable_dsts =
            child_graph.parentable_dsts(child_constructor.def_id, &child_constructor.body);
        let parent_body = &self.body;
        let translate_to_parent = |child: Place<'tcx>| -> Option<Place<'tcx>> {
            calling_convention.translate_to_parent(
                child,
                &self.async_info,
                self.tcx,
                parent_body,
                self.def_id.to_def_id(),
                destination,
            )
        };

        // For each destination node CHILD that is parentable to PLACE,
        // add an edge from CHILD -> PLACE.
        //
        // PRECISION TODO: for a given child place, we only want to connect
        // the *last* nodes in the child function to the parent, not *all* of them.
        trace!("CHILD -> PARENT EDGES:");
        for (child_dst, _) in parentable_dsts {
            if let Some(parent_place) = translate_to_parent(child_dst.place) {
                self.apply_mutation(state, location, parent_place);
            }
        }
        trace!(
            "  Inlined {}",
            self.fmt_fn(child_constructor.def_id.to_def_id())
        );

        Some(())
    }

    fn modular_mutation_visitor<'a>(
        &'a self,
        state: &'a mut InstructionState<'tcx>,
    ) -> ModularMutationVisitor<'a, 'tcx, impl FnMut(Location, Mutation<'tcx>) + 'a> {
        ModularMutationVisitor::new(
            &self.place_info,
            move |location, mutation: Mutation<'tcx>| {
                self.apply_mutation(state, location, mutation.mutated)
            },
        )
    }

    fn handle_terminator(
        &self,
        terminator: &Terminator<'tcx>,
        state: &mut InstructionState<'tcx>,
        location: Location,
        time: Time,
    ) {
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            if self
                .handle_call(state, location, func, args, *destination)
                .is_none()
            {
                trace!("Terminator {:?} failed the preamble", terminator.kind);
                self.terminator_visitor(state, time)
                    .visit_terminator(terminator, location)
            }
        } else {
            // Fallback: call the visitor
            self.terminator_visitor(state, time)
                .visit_terminator(terminator, location)
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
            .iterate_to_fixpoint();

        let mut final_state = PartialGraph::default();

        analysis.visit_reachable_with(&self.body, &mut final_state);

        let all_returns = self.body.all_returns().map(|ret| ret.block).collect_vec();
        let has_return = !all_returns.is_empty();
        let mut analysis = analysis.into_results_cursor(&self.body);
        if has_return {
            for block in all_returns {
                analysis.seek_to_block_end(block);
                let return_state = analysis.get();
                for (place, locations) in &return_state.last_mutation {
                    let ret_kind = if place.local == RETURN_PLACE {
                        TargetUse::Return
                    } else if let Some(num) = other_as_arg(*place, &self.body) {
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

    fn terminator_visitor<'a>(
        &'a self,
        state: &'a mut InstructionState<'tcx>,
        time: Time,
    ) -> ModularMutationVisitor<'a, 'tcx, impl FnMut(Location, Mutation<'tcx>) + 'a> {
        let mut vis = self.modular_mutation_visitor(state);
        vis.set_time(time);
        vis
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

enum CallHandling<'tcx, 'a> {
    ApproxAsyncFn,
    Ready(GraphConstructor<'tcx>, CallingConvention<'tcx, 'a>),
    ApproxAsyncSM(
        fn(
            &GraphConstructor<'tcx>,
            &mut dyn Visitor<'tcx>,
            &[Operand<'tcx>],
            Place<'tcx>,
            Location,
        ),
    ),
}

struct DfAnalysis<'a, 'tcx>(&'a GraphConstructor<'tcx>);

impl<'tcx> df::AnalysisDomain<'tcx> for DfAnalysis<'_, 'tcx> {
    type Domain = InstructionState<'tcx>;

    const NAME: &'static str = "GraphConstructor";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        InstructionState::default()
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
        self.0
            .handle_terminator(terminator, state, location, Time::Unspecified);
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
