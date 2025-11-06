use std::{borrow::Cow, fmt, hash::Hash, rc::Rc};

use either::Either;
use log::trace;

use flowistry_pdg::{Constant, GlobalLocation};

use df::ResultsVisitor;
use rustc_errors::DiagMessage;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{visit::Visitor, AggregateKind, Location, Place, Rvalue, Terminator, TerminatorKind},
    ty::{Instance, TyCtxt, TypingEnv},
};
use rustc_mir_dataflow::{self as df, Results};

use super::{
    async_support::*,
    calling_convention::PlaceTranslator,
    local::{CallHandling, InstructionState, LocalAnalysis},
    mutation::{ModularMutationVisitor, Mutation, Time},
};
use crate::{
    callback::DefaultCallback,
    constants::PlaceOrConst,
    source_access::{self, BodyCache, CachedBody},
    utils::{manufacture_substs_for, try_resolve_function, TwoLevelCache},
    CallChangeCallback,
};

pub mod call_tree_visit;
mod graph_elems;
mod partial_graph;

use call_tree_visit::VisitDriver;
pub use graph_elems::{DepEdge, DepEdgeKind, DepNode, DepNodeKind, OneHopLocation, Use};
pub use partial_graph::{Node, NodeKey, PartialGraph};

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
pub struct MemoPdgConstructor<'tcx, K> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) call_change_callback: Rc<dyn CallChangeCallback<'tcx, K> + 'tcx>,
    pub(crate) dump_mir: bool,
    pub(crate) async_info: Rc<AsyncInfo>,
    pub pdg_cache: PdgCache<'tcx, K>,
    pub(crate) body_cache: Rc<source_access::BodyCache<'tcx>>,
    disable_cache: bool,
    relaxed: bool,
}

impl<'tcx, K: Default> MemoPdgConstructor<'tcx, K> {
    /// Initialize the constructor.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self::new_with_callbacks(tcx, DefaultCallback)
    }
    /// Initialize the constructor.
    pub fn new_with_cache(
        tcx: TyCtxt<'tcx>,
        body_cache: Rc<source_access::BodyCache<'tcx>>,
    ) -> Self {
        Self {
            tcx,
            call_change_callback: Rc::new(DefaultCallback),
            dump_mir: false,
            async_info: AsyncInfo::make(tcx).expect("Async functions are not defined"),
            pdg_cache: Default::default(),
            body_cache,
            disable_cache: false,
            relaxed: false,
        }
    }
}

impl<'tcx, K> MemoPdgConstructor<'tcx, K> {
    /// Initialize the constructor.
    pub fn new_with_callbacks(
        tcx: TyCtxt<'tcx>,
        callback: impl CallChangeCallback<'tcx, K> + 'tcx,
    ) -> Self {
        Self {
            tcx,
            call_change_callback: Rc::new(callback),
            dump_mir: false,
            async_info: AsyncInfo::make(tcx).expect("Async functions are not defined"),
            pdg_cache: Default::default(),
            body_cache: Rc::new(BodyCache::new(tcx)),
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
        callback: impl CallChangeCallback<'tcx, K> + 'tcx,
    ) -> &mut Self {
        self.call_change_callback = Rc::new(callback);
        self
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
    pub fn take_call_changes_policy(&mut self) -> Rc<dyn CallChangeCallback<'tcx, K> + 'tcx> {
        self.call_change_callback.clone()
    }

    pub(crate) fn maybe_span_err(&self, span: rustc_span::Span, msg: impl Into<DiagMessage>) {
        if self.relaxed {
            self.tcx.dcx().span_warn(span, msg.into());
        } else {
            self.tcx.dcx().span_err(span, msg.into());
        }
    }

    pub fn strict(&self) -> bool {
        !self.relaxed
    }
}

impl<'tcx, K: std::hash::Hash + Eq + Clone> MemoPdgConstructor<'tcx, K> {
    pub fn create_root_key(&self, function: LocalDefId) -> (Instance<'tcx>, K) {
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

        (resolution, self.call_change_callback.root_k(resolution))
    }

    /// Construct the intermediate PDG for this function. Instantiates any
    /// generic arguments as `dyn <constraints>`.
    pub fn construct_root<'a>(&'a self, function: LocalDefId) -> Cow<'a, PartialGraph<'tcx, K>> {
        let key = self.create_root_key(function);
        self.construct_for(key.clone()).unwrap_or_msg(|| {
            format!(
                "Failed to construct PDG for {function:?} with generics {:?}",
                key.0.args
            )
        })
    }

    /// Construct a  graph for this instance of return it from the cache.
    ///
    /// Returns `None` if this is a recursive call trying to construct the graph again.
    pub(crate) fn construct_for<'a>(
        &'a self,
        descriptor: (Instance<'tcx>, K),
    ) -> ConstructionResult<Cow<'a, PartialGraph<'tcx, K>>> {
        let (resolution, k) = descriptor.clone();
        let mut construct = Some(|| {
            let g = LocalAnalysis::new(self, resolution, k)?.construct_partial();
            Some(g)
        });
        let mut was_constructed = false;
        let result = self.pdg_cache.get_maybe_recursive(descriptor, |_| {
            was_constructed = true;
            (construct.take().unwrap())()
        });
        if self.disable_cache && result.is_some() && !was_constructed {
            return (construct.take().unwrap())()
                .map_or(ConstructionResult::Unconstructible, |r| {
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
    pub fn is_in_cache(&self, resolution: PdgCacheKey<'tcx, K>) -> bool {
        self.pdg_cache.is_in_cache(&resolution)
    }

    pub fn is_recursion(&self, instance: Instance<'tcx>) -> bool {
        // This should be provided by the cache itself.
        self.pdg_cache
            .as_ref()
            .borrow()
            .get(&instance)
            .is_some_and(|v| v.0)
    }
}

type LocalAnalysisResults<'tcx, 'mir, K> = Results<'tcx, &'mir LocalAnalysis<'tcx, 'mir, K>>;

impl<'mir, 'tcx, K: Hash + Eq + Clone>
    ResultsVisitor<'mir, 'tcx, &'mir LocalAnalysis<'tcx, 'mir, K>> for PartialGraph<'tcx, K>
{
    fn visit_after_early_statement_effect(
        &mut self,
        results: &mut LocalAnalysisResults<'tcx, 'mir, K>,
        state: &InstructionState<'tcx>,
        statement: &'mir rustc_middle::mir::Statement<'tcx>,
        location: Location,
    ) {
        let mut vis = self.modular_mutation_visitor(results, state, results.analysis.strict());

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
        results: &mut LocalAnalysisResults<'tcx, 'mir, K>,
        state: &InstructionState<'tcx>,
        terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
        if let TerminatorKind::SwitchInt { discr, .. } = &terminator.kind {
            if let Some(place) = discr.place() {
                self.register_mutation(
                    results,
                    state,
                    &[Input::Unresolved { place, use_: None }],
                    Either::Left(place),
                    location,
                    Use::Other,
                );
            }
            return;
        }

        if self.handle_as_inline(results, state, terminator, location) {
            return;
        }
        trace!("Handling terminator {:?} as not inlined", terminator.kind);
        let mut arg_vis = self.modular_mutation_visitor(results, state, results.analysis.strict());
        arg_vis.set_time(Time::Before);
        arg_vis.visit_terminator(terminator, location);
    }

    fn visit_after_primary_terminator_effect(
        &mut self,
        results: &mut LocalAnalysisResults<'tcx, 'mir, K>,
        state: &InstructionState<'tcx>,
        terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
            let handling = results.analysis.determine_call_handling(
                location,
                Cow::Borrowed(func),
                Cow::Borrowed(args),
                terminator.source_info.span,
            );
            match handling {
                Some(CallHandling::Ready { .. }) | Some(CallHandling::ApproxAsyncSM(_)) => {
                    // I'm not totally sure whether we need to call the
                    // approximation handler again here
                    return;
                }
                _ => (),
            }
        }

        trace!("Handling terminator {:?} as not inlined", terminator.kind);
        let mut arg_vis = self.modular_mutation_visitor(results, state, results.analysis.strict());
        arg_vis.set_time(Time::After);
        arg_vis.visit_terminator(terminator, location);
    }
}

impl<'tcx, K: Hash + Eq + Clone> PartialGraph<'tcx, K> {
    fn modular_mutation_visitor<'a, 'mir>(
        &'a mut self,
        results: &'a LocalAnalysisResults<'tcx, 'mir, K>,
        state: &'a InstructionState<'tcx>,
        strict: bool,
    ) -> ModularMutationVisitor<
        'a,
        'tcx,
        impl FnMut(Location, Mutation<'tcx>) + use<'a, 'tcx, 'mir, K>,
    > {
        ModularMutationVisitor::new(
            &results.analysis.place_info,
            results.analysis.param_env,
            move |location, mutation| {
                let place = results.analysis.normalize_place(&mutation.mutated);
                let inputs = mutation
                    .inputs
                    .into_iter()
                    .map(|(place, o)| match place {
                        PlaceOrConst::Place(place) => Input::Unresolved {
                            place: results.analysis.normalize_place(&place),
                            use_: o,
                        },
                        PlaceOrConst::Const(const_) => Input::Const {
                            const_,
                            span: results.analysis.place_info.body.source_info(location).span,
                            is_arg: o,
                        },
                    })
                    .collect::<Box<_>>();
                self.register_mutation(
                    results,
                    state,
                    &inputs,
                    Either::Left(place),
                    location,
                    mutation.is_arg,
                )
            },
            strict,
        )
    }

    /// returns whether we were able to successfully handle this as inline
    fn handle_as_inline<'a>(
        &mut self,
        results: &LocalAnalysisResults<'tcx, 'a, K>,
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
        let strict = constructor.strict();
        let Some(handling) = constructor.determine_call_handling(
            location,
            Cow::Borrowed(func),
            Cow::Borrowed(args),
            terminator.source_info.span,
        ) else {
            return false;
        };

        let ((child_instance, k), child_descriptor, calling_convention, precise) = match handling {
            CallHandling::Ready {
                calling_convention,
                descriptor,
                precise,
            } => (
                descriptor.clone(),
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
                    IndexVec::from_iter(args.iter().map(|op| op.node.clone())),
                );

                self.modular_mutation_visitor(results, state, strict)
                    .visit_assign(destination, &rvalue, location);
                return false;
            }
            CallHandling::ApproxAsyncSM(how) => {
                how(
                    constructor,
                    &mut self.modular_mutation_visitor(results, state, strict),
                    args,
                    *destination,
                    location,
                );
                return false;
            }
        };
        // XXX: We ignore constants here, but maybe they should actually be
        // propagated up and into the PDG.
        let ctrl_inputs = constructor
            .find_control_inputs(location)
            .into_iter()
            .filter_map(|(place, loc, edge)| Some((self.get_place_node(place, loc)?, edge)))
            .collect();
        self.inlined_calls
            .push((location, child_instance, k, ctrl_inputs));
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
        for child_src in child_graph.parentable_srcs() {
            let child_src = child_src.map_at(|b| bool_to_loc(*b));
            let Some(child_place) = child_src.place() else {
                continue;
            };
            let child_node = self.get_or_construct_node(
                &NodeKey::for_place(child_place, child_src.at.clone()),
                || child_src,
            );
            if let Some(translation) = translator.translate_to_parent(child_place) {
                self.register_mutation(
                    results,
                    state,
                    &[Input::Unresolved {
                        place: translation,
                        use_: None,
                    }],
                    Either::Right(child_node),
                    location,
                    Use::Other,
                );
            }
        }

        // For each destination node CHILD that is parentable to PLACE,
        // add an edge from CHILD -> PLACE.
        //
        // PRECISION TODO: for a given child place, we only want to connect
        // the *last* nodes in the child function to the parent, not *all* of them.
        trace!("CHILD -> PARENT EDGES for {:?}:", child_graph.def_id);
        for child_dst in child_graph.parentable_dsts() {
            let child_dst = child_dst.map_at(|b| bool_to_loc(*b));
            let Some(child_place) = child_dst.place() else {
                continue;
            };
            let child_node = self.get_or_construct_node(
                &NodeKey::for_place(child_place, child_dst.at.clone()),
                || child_dst,
            );
            if let Some(parent_place) = translator.translate_to_parent(child_place) {
                self.register_mutation(
                    results,
                    state,
                    &[Input::Resolved { node: child_node }],
                    Either::Left(parent_place),
                    location,
                    Use::Other,
                );
            }
        }
        trace!("Call handling finished");
        true
    }

    fn register_mutation(
        &mut self,
        results: &LocalAnalysisResults<'tcx, '_, K>,
        state: &InstructionState<'tcx>,
        inputs: &[Input<'tcx>],
        mutated: Either<Place<'tcx>, Node>,
        location: Location,
        use_: Use,
    ) where
        K: Hash + Eq + Clone,
    {
        //println!("Mutation on {mutated:?}");
        trace!("Registering mutation to {mutated:?} with inputs {inputs:?} at {location:?}");
        let constructor = &results.analysis;
        let ctrl_inputs = constructor.find_control_inputs(location);

        trace!("  Found control inputs {ctrl_inputs:?}");

        let data_inputs = inputs
            .iter()
            .flat_map(|i| match i {
                Input::Unresolved { place, use_ } => Either::Right(
                    constructor
                        .find_data_inputs(state, *place)
                        .into_iter()
                        .map(|(place, at)| {
                            self.get_or_construct_node(
                                &NodeKey::for_place(place, at.into()),
                                || {
                                    constructor.make_dep_node(
                                        place,
                                        at,
                                        use_.map_or(Use::Other, Use::Arg),
                                    )
                                },
                            )
                        })
                        .collect::<Vec<_>>()
                        .into_iter(),
                ),
                Input::Const {
                    const_: value,
                    span,
                    is_arg,
                } => Either::Left(std::iter::once(self.get_or_construct_node(
                    &NodeKey::for_const(*value, *is_arg, location.into()),
                    || DepNode {
                        kind: DepNodeKind::Const(*value),
                        at: location.into(),
                        span: *span,
                        use_: is_arg.map_or(Use::Other, Use::Arg),
                    },
                ))),
                Input::Resolved { node } => Either::Left(std::iter::once(*node)),
            })
            .collect::<Vec<_>>();
        trace!("  Data inputs: {data_inputs:?}");

        let outputs = match mutated {
            Either::Right(node) => vec![node],
            Either::Left(place) => results
                .analysis
                .find_outputs(place, location)
                .into_iter()
                .map(|(place, at)| {
                    let key = NodeKey::for_place(place, at.into());
                    self.get_or_construct_node(&key, || constructor.make_dep_node(place, at, use_))
                })
                .collect(),
        };
        trace!("  Outputs: {outputs:?}");

        // Add data dependencies: data_input -> output
        for data_input in data_inputs {
            let data_edge = DepEdge::data(location.into());
            for output in &outputs {
                trace!("  Adding edge {data_input:?} -> {output:?}");
                self.insert_edge(data_input, *output, data_edge.clone());
            }
        }

        // Add control dependencies: ctrl_input -> output
        for (ctrl_input, loc, edge) in &ctrl_inputs {
            let from = self
                .get_or_construct_node(&NodeKey::for_place(*ctrl_input, loc.clone()), || {
                    constructor.make_dep_node(*ctrl_input, loc.location, Use::Other)
                });
            for output in &outputs {
                self.insert_edge(from, *output, edge.clone());
            }
        }
    }
}

/// How we are indexing into [`PdgCache`]
pub type PdgCacheKey<'tcx, K> = (Instance<'tcx>, K);
/// Stores PDG's we have already computed and which we know we can use again
/// given a certain key.
pub type PdgCache<'tcx, K> = Rc<TwoLevelCache<Instance<'tcx>, K, Option<PartialGraph<'tcx, K>>>>;

#[derive(Debug)]
enum Input<'tcx> {
    Unresolved {
        place: Place<'tcx>,
        use_: Option<u16>,
    },
    Const {
        const_: Constant,
        span: rustc_span::Span,
        is_arg: Option<u16>,
    },
    Resolved {
        node: Node,
    },
}

struct GraphSizeEstimator {
    nodes: usize,
    edges: usize,
    functions: usize,
    max_call_string: Box<[GlobalLocation]>,
}

#[allow(dead_code)]
impl GraphSizeEstimator {
    fn new() -> Self {
        Self {
            nodes: 0,
            edges: 0,
            max_call_string: Box::new([]),
            functions: 0,
        }
    }

    fn format_size(&self) -> String {
        format!(
            "nodes: {}, edges: {}, functions: {}, call_string_length: {}",
            HumanInt(self.nodes),
            HumanInt(self.edges),
            HumanInt(self.functions),
            HumanInt(self.max_call_string.len()),
        )
    }

    #[allow(dead_code)]
    fn format_max_call_string(&self, tcx: TyCtxt<'_>) -> String {
        self.max_call_string
            .iter()
            .map(|loc| {
                format!(
                    "  {} ({:?})\n    {:?}",
                    tcx.def_path_str(loc.function),
                    loc.location,
                    tcx.def_span(loc.function)
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    }
}

impl<'tcx, K: Hash + Eq + Clone> call_tree_visit::Visitor<'tcx, K> for GraphSizeEstimator {
    fn visit_partial_graph(
        &mut self,
        vis: &mut VisitDriver<'tcx, '_, K>,
        graph: &PartialGraph<'tcx, K>,
    ) {
        self.nodes += graph.node_count();
        self.edges += graph.edge_count();
        self.functions += 1;
        let call_string = vis.call_stack();
        if self.max_call_string.len() < call_string.len() {
            self.max_call_string = call_string.into();
        }
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
