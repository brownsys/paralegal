use std::{borrow::Cow, fmt, rc::Rc};

use either::Either;
use flowistry::mir::FlowistryInput;
use log::trace;
use petgraph::graph::{DiGraph, NodeIndex};

use flowistry_pdg::{CallString, GlobalLocation, RichLocation};

use df::{AnalysisDomain, Results, ResultsVisitor};
use rustc_error_messages::DiagnosticMessage;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{visit::Visitor, AggregateKind, Location, Place, Rvalue, Terminator, TerminatorKind},
    ty::{Instance, TyCtxt},
};
use rustc_mir_dataflow::{self as df};

use rustc_utils::cache::Cache;

use crate::{
    async_support::*,
    body_cache::{self, BodyCache, CachedBody},
    call_tree_visit::{self, VisitDriver},
    calling_convention::PlaceTranslator,
    graph::{DepEdge, DepGraph, DepNode, OneHopLocation, PartialGraph, SourceUse, TargetUse},
    local_analysis::{CallHandling, InstructionState, LocalAnalysis},
    mutation::{ModularMutationVisitor, Mutation, Time},
    utils::{manufacture_substs_for, try_resolve_function},
    CallChangeCallback,
};

#[derive(Debug, Clone, Copy)]
pub enum ConstructionResult<T> {
    Success(T),
    Recursive,
    /// The body could not be loaded. At the moment this means this is an extern item.
    Unconstructible,
}

impl<T> ConstructionResult<T> {
    pub fn unwrap(self) -> T {
        match self {
            ConstructionResult::Success(t) => t,
            ConstructionResult::Recursive => panic!("Recursion detected"),
            ConstructionResult::Unconstructible => panic!("Unconstructible body"),
        }
    }

    pub fn unwrap_or_msg(self, msg: impl FnOnce() -> String) -> T {
        match self {
            ConstructionResult::Success(t) => t,
            ConstructionResult::Recursive => panic!("Recursion detected: {}", msg()),
            ConstructionResult::Unconstructible => panic!("Unconstrutible body: {}", msg()),
        }
    }

    pub fn expect(self, msg: &str) -> T {
        match self {
            ConstructionResult::Success(t) => t,
            ConstructionResult::Recursive => panic!("Recursion detected: {}", msg),
            ConstructionResult::Unconstructible => panic!("Unconstrutible body: {}", msg),
        }
    }
}

/// A memoizing constructor of PDGs.
///
/// Each `(LocalDefId, GenericArgs)` pair is guaranteed to be constructed only
/// once.
pub struct MemoPdgConstructor<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) call_change_callback: Option<Rc<dyn CallChangeCallback<'tcx> + 'tcx>>,
    pub(crate) dump_mir: bool,
    pub(crate) async_info: Rc<AsyncInfo>,
    pub pdg_cache: PdgCache<'tcx>,
    pub(crate) body_cache: Rc<body_cache::BodyCache<'tcx>>,
    disable_cache: bool,
    relaxed: bool,
}

impl<'tcx> MemoPdgConstructor<'tcx> {
    /// Initialize the constructor.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            call_change_callback: None,
            dump_mir: false,
            async_info: AsyncInfo::make(tcx).expect("Async functions are not defined"),
            pdg_cache: Default::default(),
            body_cache: Rc::new(BodyCache::new(tcx)),
            disable_cache: false,
            relaxed: false,
        }
    }

    /// Initialize the constructor.
    pub fn new_with_cache(tcx: TyCtxt<'tcx>, body_cache: Rc<body_cache::BodyCache<'tcx>>) -> Self {
        Self {
            tcx,
            call_change_callback: None,
            dump_mir: false,
            async_info: AsyncInfo::make(tcx).expect("Async functions are not defined"),
            pdg_cache: Default::default(),
            body_cache,
            disable_cache: false,
            relaxed: false,
        }
    }

    pub fn with_disable_cache(&mut self, disable_cache: bool) -> &mut Self {
        self.disable_cache = disable_cache;
        self
    }

    /// Dump the MIR of any function that is visited.
    pub fn with_dump_mir(&mut self, dump_mir: bool) -> &mut Self {
        self.dump_mir = dump_mir;
        self
    }

    pub fn with_relaxed(&mut self, relaxed: bool) -> &mut Self {
        self.relaxed = relaxed;
        self
    }

    /// Register a callback to determine how to deal with function calls seen.
    /// Overwrites any previously registered callback with no warning.
    pub fn with_call_change_callback(
        &mut self,
        callback: impl CallChangeCallback<'tcx> + 'tcx,
    ) -> &mut Self {
        self.call_change_callback.replace(Rc::new(callback));
        self
    }

    /// Construct the intermediate PDG for this function. Instantiates any
    /// generic arguments as `dyn <constraints>`.
    pub fn construct_root<'a>(&'a self, function: LocalDefId) -> Cow<'a, PartialGraph<'tcx>> {
        let generics = manufacture_substs_for(self.tcx, function.to_def_id())
            .map_err(|i| vec![i])
            .unwrap();
        let resolution = try_resolve_function(
            self.tcx,
            function.to_def_id(),
            self.tcx.param_env_reveal_all_normalized(function),
            generics,
        )
        .unwrap();

        self.construct_for(resolution).unwrap_or_msg(|| {
            format!("Failed to construct PDG for {function:?} with generics {generics:?}")
        })
    }

    /// Construct a  graph for this instance of return it from the cache.
    ///
    /// Returns `None` if this is a recursive call trying to construct the graph again.
    pub(crate) fn construct_for<'a>(
        &'a self,
        resolution: Instance<'tcx>,
    ) -> ConstructionResult<Cow<'a, PartialGraph<'tcx>>> {
        let construct = || {
            let g = LocalAnalysis::new(self, resolution)?.construct_partial();
            Some(g)
        };
        let mut was_constructed = false;
        let result = self.pdg_cache.get_maybe_recursive(resolution, |_| {
            was_constructed = true;
            construct()
        });
        if self.disable_cache && result.is_some() && !was_constructed {
            return construct().map_or(ConstructionResult::Unconstructible, |r| {
                ConstructionResult::Success(Cow::Owned(r))
            });
        }
        match result {
            None => ConstructionResult::Recursive,
            Some(None) => ConstructionResult::Unconstructible,
            Some(Some(g)) => ConstructionResult::Success(Cow::Borrowed(g)),
        }
    }

    /// Has a PDG been constructed for this instance before?
    pub fn is_in_cache(&self, resolution: PdgCacheKey<'tcx>) -> bool {
        self.pdg_cache.is_in_cache(&resolution)
    }

    /// Construct a final PDG for this function. Same as
    /// [`Self::construct_root`] this instantiates all generics as `dyn`.
    ///
    /// Additionally if this is an `async fn` or `#[async_trait]` it will inline
    /// the closure as though the function were called with `poll`.
    pub fn construct_graph(&self, function: LocalDefId) -> DepGraph<'tcx> {
        if let Some((generator, loc, _ty)) = determine_async(
            self.tcx,
            function.to_def_id(),
            self.body_cache.try_get(function.to_def_id()).unwrap_or_else(|| panic!("INVARIANT VIOLATED: body for local function {function:?} cannot be loaded.")).body(),
        ) {
            // TODO remap arguments

            // Note that this deliberately register this result in a separate
            // cache. This is because when this async fn is called somewhere we
            // don't want to use this "fake inlined" version.
            self.construct_root(generator.def_id().expect_local())
                .to_petgraph_with_extra_global_location(
                    self,
                    GlobalLocation {
                        function: function.to_def_id(),
                        location: flowistry_pdg::RichLocation::Location(loc),
                    }
                )
        } else {
            self.construct_root(function).to_petgraph(self)
        }
    }

    pub fn is_recursion(&self, instance: Instance<'tcx>) -> bool {
        // This should be provided by the cache itself.
        matches!(self.pdg_cache.as_ref().borrow().get(&instance), Some(None))
    }

    /// Try to retrieve or load a body for this id.
    ///
    /// Make sure the body is retrievable or this function will panic.
    pub fn body_for_def_id(&self, key: DefId) -> &'tcx CachedBody<'tcx> {
        self.body_cache.get(key)
    }

    /// Access to the underlying body cache.
    pub fn body_cache(&self) -> &Rc<BodyCache<'tcx>> {
        &self.body_cache
    }

    /// Used for testing.
    pub fn take_call_changes_policy(&mut self) -> Option<Rc<dyn CallChangeCallback<'tcx> + 'tcx>> {
        self.call_change_callback.take()
    }

    pub(crate) fn maybe_span_err(&self, span: rustc_span::Span, msg: impl Into<DiagnosticMessage>) {
        if self.relaxed {
            self.tcx.sess.span_warn(span, msg.into());
        } else {
            self.tcx.sess.span_err(span, msg.into());
        }
    }
}

type LocalAnalysisResults<'tcx, 'mir> = Results<'tcx, &'mir LocalAnalysis<'tcx, 'mir>>;

impl<'mir, 'tcx> ResultsVisitor<'mir, 'tcx, LocalAnalysisResults<'tcx, 'mir>>
    for PartialGraph<'tcx>
{
    type FlowState = <&'mir LocalAnalysis<'tcx, 'mir> as AnalysisDomain<'tcx>>::Domain;

    fn visit_statement_before_primary_effect(
        &mut self,
        results: &LocalAnalysisResults<'tcx, 'mir>,
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
        results: &LocalAnalysisResults<'tcx, 'mir>,
        state: &Self::FlowState,
        terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
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

        if self.handle_as_inline(results, state, terminator, location) {
            return;
        }
        trace!("Handling terminator {:?} as not inlined", terminator.kind);
        let mut arg_vis =
            ModularMutationVisitor::new(&results.analysis.place_info, move |location, mutation| {
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
            });
        arg_vis.set_time(Time::Before);
        arg_vis.visit_terminator(terminator, location);
    }

    fn visit_terminator_after_primary_effect(
        &mut self,
        results: &LocalAnalysisResults<'tcx, 'mir>,
        state: &Self::FlowState,
        terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
            if matches!(
                results.analysis.determine_call_handling(
                    location,
                    Cow::Borrowed(func),
                    Cow::Borrowed(args),
                    terminator.source_info.span
                ),
                Some(CallHandling::Ready { .. })
            ) {
                return;
            }
        }

        trace!("Handling terminator {:?} as not inlined", terminator.kind);
        let mut arg_vis =
            ModularMutationVisitor::new(&results.analysis.place_info, move |location, mutation| {
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
            });
        arg_vis.set_time(Time::After);
        arg_vis.visit_terminator(terminator, location);
    }
}

impl<'tcx> PartialGraph<'tcx> {
    fn modular_mutation_visitor<'a, 'mir>(
        &'a mut self,
        results: &'a LocalAnalysisResults<'tcx, 'mir>,
        state: &'a InstructionState<'tcx>,
    ) -> ModularMutationVisitor<'a, 'tcx, impl FnMut(Location, Mutation<'tcx>) + 'a> {
        ModularMutationVisitor::new(&results.analysis.place_info, move |location, mutation| {
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

    /// returns whether we were able to successfully handle this as inline
    fn handle_as_inline<'a>(
        &mut self,
        results: &LocalAnalysisResults<'tcx, 'a>,
        state: &'a InstructionState<'tcx>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) -> bool {
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            return false;
        };
        let constructor = &results.analysis;
        let Some(handling) = constructor.determine_call_handling(
            location,
            Cow::Borrowed(func),
            Cow::Borrowed(args),
            terminator.source_info.span,
        ) else {
            return false;
        };

        let (child_instance, child_descriptor, calling_convention, precise) = match handling {
            CallHandling::Ready {
                calling_convention,
                descriptor,
                precise,
            } => (
                descriptor,
                constructor
                    .memo
                    .construct_for(descriptor)
                    .expect("Recursion check should have already happened"),
                calling_convention,
                precise,
            ),
            CallHandling::ApproxAsyncFn => {
                // Register a synthetic assignment of `future = (arg0, arg1, ...)`.
                let rvalue = Rvalue::Aggregate(
                    Box::new(AggregateKind::Tuple),
                    IndexVec::from_iter(args.iter().cloned()),
                );
                self.modular_mutation_visitor(results, state).visit_assign(
                    destination,
                    &rvalue,
                    location,
                );
                return false;
            }
            CallHandling::ApproxAsyncSM(how) => {
                how(
                    constructor,
                    &mut self.modular_mutation_visitor(results, state),
                    args,
                    *destination,
                    location,
                );
                return false;
            }
        };

        self.inlined_calls.push((
            location,
            child_instance,
            constructor.find_control_inputs(location),
        ));
        let child_graph = child_descriptor.as_ref();

        trace!("Child graph has generics {:?}", child_descriptor.generics);

        let translator = PlaceTranslator::new(
            constructor.async_info(),
            constructor.def_id,
            &constructor.mono_body,
            constructor.tcx(),
            *destination,
            &calling_convention,
            precise,
        );

        let bool_to_loc = |b| OneHopLocation {
            location: location.into(),
            in_child: Some((child_instance.def_id(), b)),
        };

        // For each source node CHILD that is parentable to PLACE,
        // add an edge from PLACE -> CHILD.
        trace!("PARENT -> CHILD EDGES:");
        for (child_src, _kind) in child_graph.parentable_srcs() {
            let child_src = child_src.map_at(|b| bool_to_loc(*b));
            if let Some(translation) = translator.translate_to_parent(child_src.place) {
                self.register_mutation(
                    results,
                    state,
                    Inputs::Unresolved {
                        places: vec![(translation, None)],
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
        for (child_dst, kind) in child_graph.parentable_dsts() {
            let child_dst = child_dst.map_at(|b| bool_to_loc(*b));
            if let Some(parent_place) = translator.translate_to_parent(child_dst.place) {
                self.register_mutation(
                    results,
                    state,
                    Inputs::Resolved {
                        node: child_dst.clone(),
                        node_use: SourceUse::Operand,
                    },
                    Either::Left(parent_place),
                    location,
                    kind.map_or(TargetUse::Return, TargetUse::MutArg),
                );
            }
        }
        // self.edges.extend(
        //     constructor
        //         .find_control_inputs(location)
        //         .into_iter()
        //         .flat_map(|(ctrl_src, edge)| {
        //             child_graph
        //                 .nodes
        //                 .iter()
        //                 .map(move |dest| (ctrl_src.clone(), dest.clone(), edge.clone()))
        //         }),
        // );
        true
    }
}

impl<'tcx> PartialGraph<'tcx> {
    fn register_mutation(
        &mut self,
        results: &LocalAnalysisResults<'tcx, '_>,
        state: &InstructionState<'tcx>,
        inputs: Inputs<'tcx>,
        mutated: Either<Place<'tcx>, DepNode<'tcx, OneHopLocation>>,
        location: Location,
        target_use: TargetUse,
    ) {
        trace!("Registering mutation to {mutated:?} with inputs {inputs:?} at {location:?}");
        let constructor = &results.analysis;
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
                .find_outputs(place, location)
                .into_iter()
                .map(|t| t.1)
                .collect(),
        };
        trace!("  Outputs: {outputs:?}");

        for output in &outputs {
            trace!("  Adding node {output}");
            self.nodes.insert(output.clone());
        }

        // Add data dependencies: data_input -> output
        for (data_input, source_use) in data_inputs {
            let data_edge = DepEdge::data(location.into(), source_use, target_use);
            for output in &outputs {
                trace!("  Adding edge {data_input} -> {output}");
                self.edges
                    .insert((data_input.clone(), output.clone(), data_edge.clone()));
            }
        }

        // Add control dependencies: ctrl_input -> output
        for (ctrl_input, edge) in &ctrl_inputs {
            for output in &outputs {
                self.edges
                    .insert((ctrl_input.clone(), output.clone(), edge.clone()));
            }
        }
    }
}

/// How we are indexing into [`PdgCache`]
pub type PdgCacheKey<'tcx> = Instance<'tcx>;
/// Stores PDG's we have already computed and which we know we can use again
/// given a certain key.
pub type PdgCache<'tcx> = Rc<Cache<PdgCacheKey<'tcx>, Option<PartialGraph<'tcx>>>>;

#[derive(Debug)]
enum Inputs<'tcx> {
    Unresolved {
        places: Vec<(Place<'tcx>, Option<u8>)>,
    },
    Resolved {
        node: DepNode<'tcx, OneHopLocation>,
        node_use: SourceUse,
    },
}

struct GraphAssembler<'tcx> {
    graph: DiGraph<DepNode<'tcx, CallString>, DepEdge<CallString>>,
    nodes: FxHashMap<DepNode<'tcx, CallString>, petgraph::graph::NodeIndex>,
    control_inputs: Box<[(NodeIndex, DepEdge<CallString>)]>,
}

fn globalize_location(vis: &mut VisitDriver<'_, '_>, location: &OneHopLocation) -> CallString {
    vis.with_pushed_stack(
        GlobalLocation {
            function: vis.current_function().def_id(),
            location: location.location,
        },
        |vis| {
            if let Some((c, start)) = location.in_child {
                vis.with_pushed_stack(
                    GlobalLocation {
                        function: c,
                        location: if start {
                            RichLocation::Start
                        } else {
                            RichLocation::End
                        },
                    },
                    |vis| CallString::new(vis.call_stack()),
                )
            } else {
                CallString::new(vis.call_stack())
            }
        },
    )
}

fn globalize_node<'tcx>(
    vis: &mut VisitDriver<'tcx, '_>,
    node: &DepNode<'tcx, OneHopLocation>,
) -> DepNode<'tcx, CallString> {
    node.map_at(|location| globalize_location(vis, location))
}

fn globalize_edge(
    vis: &mut VisitDriver<'_, '_>,
    edge: &DepEdge<OneHopLocation>,
) -> DepEdge<CallString> {
    edge.map_at(|location| globalize_location(vis, location))
}

impl<'tcx> GraphAssembler<'tcx> {
    fn new() -> Self {
        Self {
            graph: DiGraph::new(),
            nodes: FxHashMap::default(),
            control_inputs: Box::new([]),
        }
    }

    fn add_node(&mut self, node: DepNode<'tcx, CallString>) -> petgraph::graph::NodeIndex {
        *self
            .nodes
            .entry(node.clone())
            .or_insert_with(|| self.graph.add_node(node))
    }

    /// Forwarding of control flow. It is sound to replace the control inputs
    /// here rather than extend them because we are guaranteed that these new
    /// nodes are connected to the old ctrl nodes, possibly transitively.
    ///
    /// Each node in our graph is either connected to a local control flow
    /// node or to the ones coming from the parent, which is established by
    /// the `visit_partial_graph` function. By induction all nodes, including
    /// these control flow sources are connected to the old ctrl inputs.
    fn with_new_ctr_inputs<'c, F, R>(
        &mut self,
        vis: &mut VisitDriver<'tcx, 'c>,
        new_ctrl_inputs: &[(DepNode<'tcx, OneHopLocation>, DepEdge<OneHopLocation>)],
        f: F,
    ) -> R
    where
        F: FnOnce(&mut Self, &mut VisitDriver<'tcx, 'c>) -> R,
    {
        let new_ctrl_inputs: Box<[(NodeIndex, DepEdge<CallString>)]> = new_ctrl_inputs
            .iter()
            .map(|(src, edge)| {
                let src = globalize_node(vis, src);
                let src_idx = self.add_node(src);
                let new_edge = globalize_edge(vis, edge);
                (src_idx, new_edge)
            })
            .collect();
        // The last thing we need to ensure for that to hold is that the new
        // ctrl inputs must not be empty. So if they are we leave the old one's intact.
        let old_ctrl_inputs = if new_ctrl_inputs.is_empty() {
            Box::new([])
        } else {
            std::mem::replace(&mut self.control_inputs, new_ctrl_inputs)
        };
        let r = f(self, vis);
        if !old_ctrl_inputs.is_empty() {
            self.control_inputs = old_ctrl_inputs;
        }
        r
    }
}

impl<'tcx> call_tree_visit::Visitor<'tcx> for GraphAssembler<'tcx> {
    fn visit_inlined_call(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_>,
        loc: Location,
        inst: Instance<'tcx>,
        ctrl_inputs: &[(DepNode<'tcx, OneHopLocation>, DepEdge<OneHopLocation>)],
    ) {
        self.with_new_ctr_inputs(vis, ctrl_inputs, |slf, vis| {
            vis.visit_inlined_call(slf, loc, inst)
        })
    }

    fn visit_edge(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_>,
        src: &DepNode<'tcx, OneHopLocation>,
        dst: &DepNode<'tcx, OneHopLocation>,
        kind: &DepEdge<OneHopLocation>,
    ) {
        let src = globalize_node(vis, src);
        let src_idx = self.add_node(src);
        let dst = globalize_node(vis, dst);
        let dst_idx = self.add_node(dst);
        let new_kind = globalize_edge(vis, kind);
        self.graph.add_edge(src_idx, dst_idx, new_kind);
    }

    fn visit_partial_graph(&mut self, vis: &mut VisitDriver<'tcx, '_>, graph: &PartialGraph<'tcx>) {
        vis.visit_partial_graph(self, graph);

        // This loop connects the control inputs that
        // are incoming to the function to those nodes in the graph who have no
        // control inputs yet.
        //
        // We do this here instead of in "visit_node", because that gets called
        // before the "visit_edge" function, meaning we can't yet see the
        // potential control inputs of the node. We could have the visitor use
        // an opposite ordering, but that is counterintuitive to other potential
        // users of the visitor.
        for node in &graph.nodes {
            let new_node = globalize_node(vis, node);
            let node = self.add_node(new_node);

            if !self
                .graph
                .edges_directed(node, petgraph::Direction::Incoming)
                .any(|e| e.weight().is_control())
            {
                for (src, edge) in self.control_inputs.iter() {
                    self.graph.add_edge(*src, node, edge.clone());
                }
            }
        }
    }
}

struct GraphSizeEstimator {
    nodes: usize,
    edges: usize,
    functions: usize,
}

impl GraphSizeEstimator {
    fn new() -> Self {
        Self {
            nodes: 0,
            edges: 0,
            functions: 0,
        }
    }
}

impl<'tcx> call_tree_visit::Visitor<'tcx> for GraphSizeEstimator {
    fn visit_partial_graph(&mut self, vis: &mut VisitDriver<'tcx, '_>, graph: &PartialGraph<'tcx>) {
        self.nodes += graph.nodes.len();
        self.edges += graph.edges.len();
        self.functions += 1;
        vis.visit_partial_graph(self, graph);
    }
}
struct HumanInt(usize);

impl fmt::Display for HumanInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let num = self.0;
        let mut as_str = num.to_string();
        let len = as_str.len();
        for i in (3..len).step_by(3) {
            as_str.insert(len - i, ',');
        }

        f.write_str(&as_str)
    }
}

fn estimate_size(vis: &mut VisitDriver<'_, '_>) -> (usize, usize, usize) {
    let mut estimator = GraphSizeEstimator::new();
    vis.start(&mut estimator);
    (estimator.nodes, estimator.edges, estimator.functions)
}

impl<'tcx> PartialGraph<'tcx> {
    pub fn to_petgraph<'c>(&self, memo: &'c MemoPdgConstructor<'tcx>) -> DepGraph<'tcx> {
        log::info!("Converting to petgraph starting from {:?}.", self.def_id);
        let mut assembler = GraphAssembler::new();
        let mut visitor = VisitDriver::new(
            memo,
            Instance::expect_resolve(
                memo.tcx,
                memo.tcx.param_env_reveal_all_normalized(self.def_id),
                self.def_id,
                self.generics,
            ),
        );
        let (nodes, endges, functions) = estimate_size(&mut visitor);
        let nodes = HumanInt(nodes);
        let edges = HumanInt(endges);
        let functions = HumanInt(functions);
        log::info!("Estimating a size of {nodes} nodes, {edges} edges and {functions} functions");
        visitor.start(&mut assembler);
        DepGraph {
            graph: assembler.graph,
        }
    }

    pub fn to_petgraph_with_extra_global_location<'c>(
        &self,
        memo: &'c MemoPdgConstructor<'tcx>,
        extra_global_location: GlobalLocation,
    ) -> DepGraph<'tcx> {
        log::info!("Converting to petgraph starting from {:?}.", self.def_id);
        let mut assembler = GraphAssembler::new();
        let mut visitor = VisitDriver::new(
            memo,
            Instance::expect_resolve(
                memo.tcx,
                memo.tcx.param_env_reveal_all_normalized(self.def_id),
                self.def_id,
                self.generics,
            ),
        );
        let (nodes, endges, functions) = estimate_size(&mut visitor);

        let nodes = HumanInt(nodes);
        let edges = HumanInt(endges);
        let functions = HumanInt(functions);
        log::info!("Estimating a size of {nodes} nodes, {edges} edges and {functions} functions");
        visitor.start(&mut assembler);
        DepGraph {
            graph: assembler.graph,
        }
    }
}
