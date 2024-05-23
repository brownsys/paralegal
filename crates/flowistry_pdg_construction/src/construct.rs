use std::{borrow::Cow, collections::HashSet, iter, rc::Rc};

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
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::{
    mir::{
        visit::Visitor, AggregateKind, BasicBlock, Body, Location, Operand, Place, PlaceElem,
        Rvalue, Statement, Terminator, TerminatorEdges, TerminatorKind, RETURN_PLACE,
    },
    ty::{GenericArg, GenericArgsRef, Instance, List, TyCtxt, TyKind},
};
use rustc_mir_dataflow::{
    self as df, fmt::DebugWithContext, Analysis, AnalysisDomain, Results, ResultsVisitor,
};
use rustc_span::ErrorGuaranteed;
use rustc_utils::{
    cache::Cache,
    mir::{borrowck_facts, control_dependencies::ControlDependencies},
    BodyExt, PlaceExt,
};

use crate::{
    async_support::*,
    calling_convention::*,
    graph::{DepEdge, DepGraph, DepNode, PartialGraph, SourceUse, TargetUse},
    mutation::{ModularMutationVisitor, Mutation, Time},
    try_resolve_function,
    utils::{self, is_non_default_trait_method, manufacture_substs_for, try_monomorphize},
    Asyncness, CallChangeCallback, CallChanges, CallInfo, InlineMissReason, SkipCall,
};

pub trait PDGLoader<'tcx> {
    fn load(&self, function: DefId) -> Option<&SubgraphDescriptor<'tcx>>;
}

pub struct NoLoader;

impl<'tcx> PDGLoader<'tcx> for NoLoader {
    fn load(&self, _: DefId) -> Option<&SubgraphDescriptor<'tcx>> {
        None
    }
}

impl<'tcx, T: PDGLoader<'tcx>> PDGLoader<'tcx> for Rc<T> {
    fn load(&self, function: DefId) -> Option<&SubgraphDescriptor<'tcx>> {
        (&**self).load(function)
    }
}

impl<'tcx, T: PDGLoader<'tcx>> PDGLoader<'tcx> for Box<T> {
    fn load(&self, function: DefId) -> Option<&SubgraphDescriptor<'tcx>> {
        (&**self).load(function)
    }
}

pub struct MemoPdgConstructor<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) call_change_callback: Option<Rc<dyn CallChangeCallback<'tcx> + 'tcx>>,
    pub(crate) dump_mir: bool,
    pub(crate) async_info: Rc<AsyncInfo>,
    pub(crate) pdg_cache: PdgCache<'tcx>,
    pub(crate) loader: Box<dyn PDGLoader<'tcx> + 'tcx>,
}

impl<'tcx> MemoPdgConstructor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, loader: impl PDGLoader<'tcx> + 'tcx) -> Self {
        Self {
            tcx,
            call_change_callback: None,
            dump_mir: false,
            async_info: AsyncInfo::make(tcx).expect("Async functions are not defined"),
            pdg_cache: Default::default(),
            loader: Box::new(loader),
        }
    }

    pub fn with_dump_mir(&mut self, dump_mir: bool) -> &mut Self {
        self.dump_mir = dump_mir;
        self
    }

    pub fn with_call_change_callback(
        &mut self,
        callback: impl CallChangeCallback<'tcx> + 'tcx,
    ) -> &mut Self {
        self.call_change_callback.replace(Rc::new(callback));
        self
    }

    pub fn construct_root<'a>(
        &'a self,
        function: LocalDefId,
    ) -> Option<&'a SubgraphDescriptor<'tcx>> {
        let generics = manufacture_substs_for(self.tcx, function.to_def_id()).unwrap();
        let resolution = try_resolve_function(
            self.tcx,
            function.to_def_id(),
            self.tcx.param_env_reveal_all_normalized(function),
            generics,
        )?;
        self.construct_for(resolution)
    }

    pub(crate) fn construct_for<'a>(
        &'a self,
        resolution: Instance<'tcx>,
    ) -> Option<&'a SubgraphDescriptor<'tcx>> {
        let def_id = resolution.def_id();
        let generics = resolution.args;
        if let Some(local) = def_id.as_local() {
            self.pdg_cache.get_maybe_recursive((local, generics), |_| {
                let g = GraphConstructor::new(self, resolution).construct_partial();
                g.check_invariants();
                g
            })
        } else {
            self.loader.load(def_id)
        }
    }

    pub fn is_in_cache(&self, resolution: Instance<'tcx>) -> bool {
        if let Some(local) = resolution.def_id().as_local() {
            self.pdg_cache.is_in_cache(&(local, resolution.args))
        } else {
            self.loader.load(resolution.def_id()).is_some()
        }
    }

    pub fn construct_graph(&self, function: LocalDefId) -> Result<DepGraph<'tcx>, ErrorGuaranteed> {
        let args = manufacture_substs_for(self.tcx, function.to_def_id())?;
        let g = self
            .construct_root(function)
            .ok_or_else(|| {
                self.tcx.sess.span_err(
                    self.tcx.def_span(function),
                    "Could not construct graph for this function",
                )
            })?
            .to_petgraph();
        Ok(g)
    }
}

#[derive(PartialEq, Eq, Default, Clone, Debug)]
pub struct InstructionState<'tcx> {
    last_mutation: FxHashMap<Place<'tcx>, FxHashSet<RichLocation>>,
}

impl<C> DebugWithContext<C> for InstructionState<'_> {}

impl<'tcx> df::JoinSemiLattice for InstructionState<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        utils::hashmap_join(
            &mut self.last_mutation,
            &other.last_mutation,
            utils::hashset_join,
        )
    }
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

        if self
            .handle_as_inline(results, state, terminator, location)
            .is_none()
        {
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
                Some(CallHandling::Ready { .. })
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
    if node.at.leaf().function != def_id.to_def_id() {
        return None;
    }
    if node.place.local == RETURN_PLACE {
        Some(None)
    } else if node.place.is_arg(body) {
        Some(Some(node.place.local.as_u32() as u8 - 1))
    } else {
        None
    }
}

impl<'tcx> PartialGraph<'tcx> {
    fn modular_mutation_visitor<'a>(
        &'a mut self,
        results: &'a Results<'tcx, DfAnalysis<'a, 'tcx>>,
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

    fn handle_as_inline(
        &mut self,
        results: &Results<'tcx, DfAnalysis<'_, 'tcx>>,
        state: &<DfAnalysis<'_, 'tcx> as AnalysisDomain<'tcx>>::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) -> Option<()> {
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
        let gloc = GlobalLocation {
            location: location.into(),
            function: constructor.def_id.to_def_id(),
        };

        let (child_descriptor, calling_convention) =
            match constructor.determine_call_handling(location, func, args)? {
                CallHandling::Ready {
                    calling_convention,
                    descriptor,
                    generic_args: _,
                } => (descriptor, calling_convention),
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
                    return Some(());
                }
                CallHandling::ApproxAsyncSM(how) => {
                    how(
                        constructor,
                        &mut self.modular_mutation_visitor(results, state),
                        args,
                        *destination,
                        location,
                    );
                    return Some(());
                }
            };

        let SubgraphDescriptor {
            graph: child_graph,
            parentable_srcs,
            parentable_dsts,
        } = push_call_string_root(child_descriptor, gloc);

        // For each source node CHILD that is parentable to PLACE,
        // add an edge from PLACE -> CHILD.
        trace!("PARENT -> CHILD EDGES:");
        for (child_src, _kind) in parentable_srcs {
            if let Some(parent_place) = calling_convention.translate_to_parent(
                child_src.place,
                &constructor.async_info(),
                constructor.tcx(),
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
                &constructor.async_info(),
                constructor.tcx(),
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
        self.nodes.extend(child_graph.nodes);
        self.edges.extend(child_graph.edges);
        self.monos.extend(child_graph.monos);
        self.monos
            .insert(CallString::single(gloc), child_descriptor.graph.generics);
        Some(())
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

type PdgCache<'tcx> = Rc<Cache<(LocalDefId, GenericArgsRef<'tcx>), SubgraphDescriptor<'tcx>>>;

pub struct GraphConstructor<'tcx, 'a> {
    pub(crate) memo: &'a MemoPdgConstructor<'tcx>,
    pub(super) root: Instance<'tcx>,
    body_with_facts: &'tcx BodyWithBorrowckFacts<'tcx>,
    pub(crate) body: Body<'tcx>,
    pub(crate) def_id: LocalDefId,
    place_info: PlaceInfo<'tcx>,
    control_dependencies: ControlDependencies<BasicBlock>,
    pub(crate) body_assignments: utils::BodyAssignments,
    start_loc: FxHashSet<RichLocation>,
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

impl<'tcx, 'a> GraphConstructor<'tcx, 'a> {
    /// Creates [`GraphConstructor`] for a function resolved as `fn_resolution` in a given `calling_context`.
    pub(crate) fn new(
        memo: &'a MemoPdgConstructor<'tcx>,
        root: Instance<'tcx>,
    ) -> GraphConstructor<'tcx, 'a> {
        let tcx = memo.tcx;
        let def_id = root.def_id().expect_local();
        let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, def_id);
        let param_env = tcx.param_env_reveal_all_normalized(def_id);
        // let param_env = match &calling_context {
        //     Some(cx) => cx.param_env,
        //     None => ParamEnv::reveal_all(),
        // };
        let body = try_monomorphize(root, tcx, param_env, &body_with_facts.body);

        if memo.dump_mir {
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

        GraphConstructor {
            memo,
            root,
            body_with_facts,
            body,
            place_info,
            control_dependencies,
            start_loc,
            def_id,
            body_assignments,
        }
    }

    fn make_dep_node(
        &self,
        place: Place<'tcx>,
        location: impl Into<RichLocation>,
    ) -> DepNode<'tcx> {
        DepNode::new(
            place,
            self.make_call_string(location),
            self.tcx(),
            &self.body,
            self.place_info.children(place).iter().any(|p| *p != place),
        )
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
                    let src = self.make_dep_node(ctrl_place, ctrl_loc);
                    let edge = DepEdge::control(at, SourceUse::Operand, TargetUse::Assign);
                    out.push((src, edge));
                }
            }
        }
        out
    }

    fn call_change_callback(&self) -> Option<&dyn CallChangeCallback<'tcx>> {
        self.memo.call_change_callback.as_ref().map(Rc::as_ref)
    }

    fn async_info(&self) -> &AsyncInfo {
        &*self.memo.async_info
    }

    fn make_call_string(&self, location: impl Into<RichLocation>) -> CallString {
        CallString::single(GlobalLocation {
            function: self.root.def_id(),
            location: location.into(),
        })
    }

    /// Returns the aliases of `place`. See [`PlaceInfo::aliases`] for details.
    pub(crate) fn aliases(&'a self, place: Place<'tcx>) -> impl Iterator<Item = Place<'tcx>> + 'a {
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
            self.tcx(),
            &self.body_with_facts.body,
            self.def_id.to_def_id(),
        );
        self.place_info.aliases(place_retyped).iter().map(|alias| {
            let mut projection = alias.projection.to_vec();
            projection.extend(&place.projection[place_retyped.projection.len()..]);
            Place::make(alias.local, &projection, self.tcx())
        })
    }

    pub(crate) fn tcx(&self) -> TyCtxt<'tcx> {
        self.memo.tcx
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
            .map(|(place_ref, _)| Place::from_ref(place_ref, self.tcx()));
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
                                new_place.projection = self.tcx().mk_place_elems(rest);
                                if new_place.ty(&self.body, self.tcx()).ty.is_box() {
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
                                self.tcx(),
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
                            self.make_dep_node(conflict, *last_mut_loc)
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
                (*dst, self.make_dep_node(*dst, location))
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
                place.ty(&self.body.local_decls, self.tcx()).ty
            }
        };
        utils::type_as_fn(self.tcx(), ty)
    }

    fn fmt_fn(&self, def_id: DefId) -> String {
        self.tcx().def_path_str(def_id)
    }

    /// Special case behavior for calls to functions used in desugaring async functions.
    ///
    /// Ensures that functions like `Pin::new_unchecked` are not modularly-approximated.
    fn can_approximate_async_functions(
        &self,
        def_id: DefId,
    ) -> Option<ApproximationHandler<'tcx, 'a>> {
        let lang_items = self.tcx().lang_items();
        if Some(def_id) == lang_items.new_unchecked_fn() {
            Some(Self::approximate_new_unchecked)
        } else if Some(def_id) == lang_items.into_future_fn()
            // FIXME: better way to get retrieve this stdlib DefId?
            || self.tcx().def_path_str(def_id) == "<F as std::future::IntoFuture>::into_future"
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
        let lang_items = self.tcx().lang_items();
        let [op] = args else {
            unreachable!();
        };
        let mut operands = IndexVec::new();
        operands.push(op.clone());
        let TyKind::Adt(adt_id, generics) = destination.ty(&self.body, self.tcx()).ty.kind() else {
            unreachable!()
        };
        assert_eq!(adt_id.did(), lang_items.pin_type().unwrap());
        let aggregate_kind =
            AggregateKind::Adt(adt_id.did(), VariantIdx::from_u32(0), generics, None, None);
        let rvalue = Rvalue::Aggregate(Box::new(aggregate_kind), operands);
        trace!("Handling new_unchecked as assign for {destination:?}");
        vis.visit_assign(&destination, &rvalue, location);
    }

    fn determine_call_handling<'b>(
        &'b self,
        location: Location,
        func: &Operand<'tcx>,
        args: &'b [Operand<'tcx>],
    ) -> Option<CallHandling<'tcx, 'b>> {
        let tcx = self.tcx();

        let (called_def_id, generic_args) = self.operand_to_def_id(func)?;
        trace!("Resolved call to function: {}", self.fmt_fn(called_def_id));

        // Monomorphize the called function with the known generic_args.
        let param_env = tcx.param_env_reveal_all_normalized(self.def_id);
        let resolved_fn =
            utils::try_resolve_function(self.tcx(), called_def_id, param_env, generic_args)?;
        let resolved_def_id = resolved_fn.def_id();
        if log_enabled!(Level::Trace) && called_def_id != resolved_def_id {
            let (called, resolved) = (self.fmt_fn(called_def_id), self.fmt_fn(resolved_def_id));
            trace!("  `{called}` monomorphized to `{resolved}`",);
        }

        if is_non_default_trait_method(tcx, resolved_def_id).is_some() {
            trace!("  bailing because is unresolvable trait method");
            return None;
        }

        if let Some(handler) = self.can_approximate_async_functions(resolved_def_id) {
            return Some(CallHandling::ApproxAsyncSM(handler));
        };

        // if !resolved_def_id.is_local() {
        //     trace!(
        //         "  Bailing because func is non-local: `{}`",
        //         tcx.def_path_str(resolved_def_id)
        //     );
        //     return None;
        // };

        let call_kind = match self.classify_call_kind(called_def_id, resolved_def_id, args) {
            Ok(cc) => cc,
            Err(async_err) => {
                if let Some(cb) = self.call_change_callback() {
                    cb.on_inline_miss(
                        resolved_fn,
                        location,
                        self.root,
                        None,
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

        let cache_key = resolved_fn;

        let is_cached = self.memo.is_in_cache(cache_key);

        let call_changes = self.call_change_callback().map(|callback| {
            let info = CallInfo {
                callee: resolved_fn,
                call_string: self.make_call_string(location),
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
        let Some(descriptor) = self.memo.construct_for(cache_key) else {
            trace!("  Bailing because cache lookup {cache_key} failed");
            return None;
        };
        Some(CallHandling::Ready {
            descriptor,
            calling_convention,
            generic_args,
        })
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
            CallHandling::Ready {
                descriptor,
                generic_args: _,
                calling_convention,
            } => (descriptor, calling_convention),
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

        let parentable_dsts = &child_constructor.parentable_dsts;
        let parent_body = &self.body;
        let translate_to_parent = |child: Place<'tcx>| -> Option<Place<'tcx>> {
            calling_convention.translate_to_parent(
                child,
                &self.async_info(),
                self.tcx(),
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

        Some(())
    }

    fn modular_mutation_visitor<'b: 'a>(
        &'b self,
        state: &'a mut InstructionState<'tcx>,
    ) -> ModularMutationVisitor<'b, 'tcx, impl FnMut(Location, Mutation<'tcx>) + 'b> {
        ModularMutationVisitor::new(
            &self.place_info,
            move |location, mutation: Mutation<'tcx>| {
                self.apply_mutation(state, location, mutation.mutated)
            },
        )
    }

    pub(super) fn generic_args(&self) -> GenericArgsRef<'tcx> {
        self.root.args
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

    pub(crate) fn construct_partial(&self) -> SubgraphDescriptor<'tcx> {
        if let Some(g) = self.try_handle_as_async() {
            return g;
        }

        let mut analysis = DfAnalysis(self)
            .into_engine(self.tcx(), &self.body)
            .iterate_to_fixpoint();

        let mut final_state = PartialGraph::new(Asyncness::No, self.generic_args());

        analysis.visit_reachable_with(&self.body, &mut final_state);

        let all_returns = self.body.all_returns().map(|ret| ret.block).collect_vec();
        let mut analysis = analysis.into_results_cursor(&self.body);
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

        SubgraphDescriptor {
            parentable_dsts: final_state
                .parentable_dsts(self.def_id, &self.body)
                .collect(),
            parentable_srcs: final_state
                .parentable_srcs(self.def_id, &self.body)
                .collect(),
            graph: final_state,
        }
    }

    /// Determine the type of call-site.
    ///
    /// The error case is if we tried to resolve this as async and failed. We
    /// know it *is* async but we couldn't determine the information needed to
    /// analyze the function, therefore we will have to approximate it.
    fn classify_call_kind<'b>(
        &'b self,
        def_id: DefId,
        resolved_def_id: DefId,
        original_args: &'b [Operand<'tcx>],
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
        self.tcx().is_closure(def_id).then_some(CallKind::Indirect)
    }

    fn terminator_visitor<'b: 'a>(
        &'b self,
        state: &'b mut InstructionState<'tcx>,
        time: Time,
    ) -> ModularMutationVisitor<'b, 'tcx, impl FnMut(Location, Mutation<'tcx>) + 'b> {
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
    AsyncPoll(Instance<'tcx>, Location, Place<'tcx>),
}

type ApproximationHandler<'tcx, 'a> = fn(
    &GraphConstructor<'tcx, 'a>,
    &mut dyn Visitor<'tcx>,
    &[Operand<'tcx>],
    Place<'tcx>,
    Location,
);

pub(crate) trait TransformCallString {
    fn transform_call_string(&self, f: impl Fn(CallString) -> CallString) -> Self;
}

impl TransformCallString for CallString {
    fn transform_call_string(&self, f: impl Fn(CallString) -> CallString) -> Self {
        f(*self)
    }
}

impl TransformCallString for DepNode<'_> {
    fn transform_call_string(&self, f: impl Fn(CallString) -> CallString) -> Self {
        Self {
            at: f(self.at),
            ..*self
        }
    }
}

impl TransformCallString for DepEdge {
    fn transform_call_string(&self, f: impl Fn(CallString) -> CallString) -> Self {
        Self {
            at: f(self.at),
            ..*self
        }
    }
}

impl<'tcx> TransformCallString for PartialGraph<'tcx> {
    fn transform_call_string(&self, f: impl Fn(CallString) -> CallString) -> Self {
        let recurse_node = |n: &DepNode<'tcx>| n.transform_call_string(&f);
        Self {
            generics: self.generics,
            asyncness: self.asyncness,
            nodes: self.nodes.iter().map(recurse_node).collect(),
            edges: self
                .edges
                .iter()
                .map(|(from, to, e)| {
                    (
                        recurse_node(from),
                        recurse_node(to),
                        e.transform_call_string(&f),
                    )
                })
                .collect(),
            monos: self
                .monos
                .iter()
                .map(|(cs, args)| (f(*cs), *args))
                .collect(),
        }
    }
}

impl<'tcx> TransformCallString for SubgraphDescriptor<'tcx> {
    fn transform_call_string(&self, f: impl Fn(CallString) -> CallString) -> Self {
        let transform_vec = |v: &Vec<(DepNode<'tcx>, Option<u8>)>| {
            v.iter()
                .map(|(n, idx)| (n.transform_call_string(&f), *idx))
                .collect::<Vec<_>>()
        };
        Self {
            graph: self.graph.transform_call_string(&f),
            parentable_dsts: transform_vec(&self.parentable_dsts),
            parentable_srcs: transform_vec(&self.parentable_srcs),
        }
    }
}

pub(crate) fn push_call_string_root<T: TransformCallString>(
    old: &T,
    new_root: GlobalLocation,
) -> T {
    old.transform_call_string(|c| c.push_front(new_root))
}

#[derive(TyEncodable, TyDecodable, Debug, Clone)]
pub struct SubgraphDescriptor<'tcx> {
    pub graph: PartialGraph<'tcx>,
    pub(crate) parentable_srcs: Vec<(DepNode<'tcx>, Option<u8>)>,
    pub(crate) parentable_dsts: Vec<(DepNode<'tcx>, Option<u8>)>,
}

impl<'tcx> SubgraphDescriptor<'tcx> {
    pub fn to_petgraph(&self) -> DepGraph<'tcx> {
        let domain = &self.graph;
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
        let root_function = self.graph.nodes.iter().next().unwrap().at.root().function;
        for n in &self.graph.nodes {
            assert_eq!(n.at.root().function, root_function);
        }
        for (_, _, e) in &self.graph.edges {
            assert_eq!(e.at.root().function, root_function);
        }
    }
}

enum CallHandling<'tcx, 'a> {
    ApproxAsyncFn,
    Ready {
        calling_convention: CallingConvention<'tcx, 'a>,
        descriptor: &'a SubgraphDescriptor<'tcx>,
        generic_args: GenericArgsRef<'tcx>,
    },
    ApproxAsyncSM(ApproximationHandler<'tcx, 'a>),
}

struct DfAnalysis<'a, 'tcx>(&'a GraphConstructor<'tcx, 'a>);

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
