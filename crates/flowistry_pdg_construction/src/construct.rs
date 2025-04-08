use std::{borrow::Cow, rc::Rc};

use either::Either;
use flowistry::mir::FlowistryInput;
use log::trace;
use petgraph::graph::DiGraph;

use flowistry_pdg::{CallString, GlobalLocation};

use df::{Results, ResultsVisitor};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{visit::Visitor, AggregateKind, Location, Place, Rvalue, Terminator, TerminatorKind},
    ty::{Instance, TyCtxt, TypingEnv},
};
use rustc_mir_dataflow as df;

use rustc_utils::cache::Cache;

use crate::{
    async_support::*,
    body_cache::{self, BodyCache, CachedBody},
    calling_convention::PlaceTranslator,
    graph::{
        push_call_string_root, DepEdge, DepGraph, DepNode, PartialGraph, SourceUse, TargetUse,
    },
    local_analysis::{CallHandling, InstructionState, LocalAnalysis},
    mutation::{ModularMutationVisitor, Mutation, Time},
    utils::{manufacture_substs_for, try_resolve_function},
    CallChangeCallback,
};

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
        }
    }

    /// Dump the MIR of any function that is visited.
    pub fn with_dump_mir(&mut self, dump_mir: bool) -> &mut Self {
        self.dump_mir = dump_mir;
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
    pub fn construct_root<'a>(&'a self, function: LocalDefId) -> &'a PartialGraph<'tcx> {
        let generics = manufacture_substs_for(self.tcx, function.to_def_id())
            .map_err(|i| vec![i])
            .unwrap();
        let resolution = try_resolve_function(
            self.tcx,
            function.to_def_id(),
            TypingEnv::post_analysis(self.tcx, function.to_def_id()),
            generics,
        )
        .unwrap();

        self.construct_for(resolution)
            .expect("Invariant broken, entrypoint cannot have been recursive.")
    }

    /// Construct a  graph for this instance of return it from the cache.
    ///
    /// Returns `None` if this is a recursive call trying to construct the graph again.
    pub(crate) fn construct_for<'a>(
        &'a self,
        resolution: Instance<'tcx>,
    ) -> Option<&'a PartialGraph<'tcx>> {
        self.pdg_cache.get_maybe_recursive(&resolution, |_| {
            let g = LocalAnalysis::new(self, resolution).construct_partial();
            trace!("Computed new for {resolution:?}");
            g.check_invariants();
            g
        })
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
            self.body_cache.get(function.to_def_id()).body(),
        ) {
            // TODO remap arguments

            // Note that this deliberately register this result in a separate
            // cache. This is because when this async fn is called somewhere we
            // don't want to use this "fake inlined" version.
            return push_call_string_root(
                self.construct_root(generator.def_id().expect_local()),
                GlobalLocation {
                    function: function.to_def_id(),
                    location: flowistry_pdg::RichLocation::Location(loc),
                },
            )
            .to_petgraph();
        }
        self.construct_root(function).to_petgraph()
    }

    /// Try to retrieve or load a body for this id.
    ///
    /// Returns `None` if the loading policy forbids loading from this crate.
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
}

type LocalAnalysisResults<'tcx, 'mir> = Results<'tcx, &'mir LocalAnalysis<'tcx, 'mir>>;

impl<'mir, 'tcx> ResultsVisitor<'mir, 'tcx, &'mir LocalAnalysis<'tcx, 'mir>>
    for PartialGraph<'tcx>
{
    fn visit_after_early_statement_effect(
        &mut self,
        results: &mut LocalAnalysisResults<'tcx, 'mir>,
        state: &InstructionState<'tcx>,
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
    fn visit_after_early_terminator_effect(
        &mut self,
        results: &mut LocalAnalysisResults<'tcx, 'mir>,
        state: &InstructionState<'tcx>,
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
                    true,
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
                    true,
                )
            });
        arg_vis.set_time(Time::Before);
        arg_vis.visit_terminator(terminator, location);
    }

    fn visit_after_primary_terminator_effect(
        &mut self,
        results: &mut LocalAnalysisResults<'tcx, 'mir>,
        state: &InstructionState<'tcx>,
        terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
            let constructor = results.analysis;

            if matches!(
                constructor.determine_call_handling(
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
                    false,
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
    ) -> ModularMutationVisitor<'a, 'tcx, impl FnMut(Location, Mutation<'tcx>) + use<'a, 'tcx, 'mir>>
    {
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
                true,
            )
        })
    }

    /// returns whether we were able to successfully handle this as inline
    fn handle_as_inline<'a>(
        &mut self,
        results: &LocalAnalysisResults<'tcx, 'a>,
        state: &InstructionState<'tcx>,
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
        let gloc = GlobalLocation {
            location: location.into(),
            function: constructor.def_id,
        };

        let Some(handling) = constructor.determine_call_handling(
            location,
            Cow::Borrowed(func),
            Cow::Borrowed(args),
            terminator.source_info.span,
        ) else {
            return false;
        };

        let (child_descriptor, calling_convention, precise) = match handling {
            CallHandling::Ready {
                calling_convention,
                descriptor,
                precise,
            } => (descriptor, calling_convention, precise),
            CallHandling::ApproxAsyncFn => {
                // Register a synthetic assignment of `future = (arg0, arg1, ...)`.
                let rvalue = Rvalue::Aggregate(
                    Box::new(AggregateKind::Tuple),
                    IndexVec::from_iter(args.iter().map(|op| op.node.clone())),
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

        let child_graph = push_call_string_root(child_descriptor, gloc);

        trace!("Child graph has generics {:?}", child_descriptor.generics);

        let is_root = |n: CallString| n.len() == 2;

        let translator = PlaceTranslator::new(
            constructor.async_info(),
            constructor.def_id,
            &constructor.mono_body,
            constructor.tcx(),
            *destination,
            &calling_convention,
            precise,
        );

        // For each source node CHILD that is parentable to PLACE,
        // add an edge from PLACE -> CHILD.
        trace!("PARENT -> CHILD EDGES:");
        for (child_src, _kind) in child_graph.parentable_srcs(is_root) {
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
                    true,
                );
            }
        }

        // For each destination node CHILD that is parentable to PLACE,
        // add an edge from CHILD -> PLACE.
        //
        // PRECISION TODO: for a given child place, we only want to connect
        // the *last* nodes in the child function to the parent, not *all* of them.
        trace!("CHILD -> PARENT EDGES:");
        for (child_dst, kind) in child_graph.parentable_dsts(is_root) {
            if let Some(parent_place) = translator.translate_to_parent(child_dst.place) {
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
                    true,
                );
            }
        }
        self.edges.extend(
            constructor
                .find_control_inputs(location)
                .into_iter()
                .flat_map(|(ctrl_src, edge)| {
                    child_graph
                        .nodes
                        .iter()
                        .map(move |dest| (ctrl_src, *dest, edge))
                }),
        );
        self.nodes.extend(child_graph.nodes);
        self.edges.extend(child_graph.edges);
        true
    }
}

impl<'tcx> PartialGraph<'tcx> {
    /// The consider_readable flag is so that the "after primary effect" phase
    /// doesn't consider overlapping places of the call arguments. Those are
    /// guaranteed to have been handled before when the reachable inputs are
    /// combined on the argument place.
    fn register_mutation(
        &mut self,
        results: &LocalAnalysisResults<'tcx, '_>,
        state: &InstructionState<'tcx>,
        inputs: Inputs<'tcx>,
        mutated: Either<Place<'tcx>, DepNode<'tcx>>,
        location: Location,
        target_use: TargetUse,
        consider_reachable: bool,
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
                        .find_data_inputs(state, input, consider_reachable)
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

/// How we are indexing into [`PdgCache`]
pub type PdgCacheKey<'tcx> = Instance<'tcx>;
/// Stores PDG's we have already computed and which we know we can use again
/// given a certain key.
pub type PdgCache<'tcx> = Rc<Cache<PdgCacheKey<'tcx>, PartialGraph<'tcx>>>;

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

impl<'tcx> PartialGraph<'tcx> {
    pub fn to_petgraph(&self) -> DepGraph<'tcx> {
        let domain = self;
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

    fn check_invariants(&self) {
        let root_function = self.nodes.iter().next().unwrap().at.root().function;
        for n in &self.nodes {
            assert_eq!(n.at.root().function, root_function);
        }
        for (_, _, e) in &self.edges {
            assert_eq!(e.at.root().function, root_function);
        }
    }
}
