//! Constructing PDGs.
//!
//! The construction is split into two steps. A local analysis and a
//! cross-procedure PDG merging.
//!
//! 1. [`GraphConstructor`] is responsible for the local analysis. It performs a
//!    procedure-local fixpoint analysis to determine a pre- and post effect
//!    [`InstructionState`] at each instruction in the procedure.
//! 2. [`PartialGraph`] implements [`ResultsVisitor`] over the analysis result

use std::{borrow::Cow, fmt::Display, rc::Rc};

use anyhow::anyhow;
use either::Either;

use flowistry_pdg::{CallString, GlobalLocation};

use log::trace;
use petgraph::graph::DiGraph;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexVec;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::{
    mir::{
        visit::Visitor, AggregateKind, Location, Operand, Place, Rvalue, Terminator, TerminatorKind,
    },
    ty::{GenericArgsRef, Instance, ParamEnv, TyCtxt},
};
use rustc_mir_dataflow::{AnalysisDomain, Results, ResultsVisitor};
use rustc_span::Span;
use rustc_utils::{cache::Cache, mir::borrowck_facts};

use crate::{
    async_support::*,
    graph::{
        push_call_string_root, DepEdge, DepGraph, DepNode, PartialGraph, SourceUse, TargetUse,
    },
    local_analysis::{CallHandling, InstructionState, LocalAnalysis},
    mutation::{ModularMutationVisitor, Mutation, Time},
    utils::{manufacture_substs_for, try_monomorphize, try_resolve_function},
    CallChangeCallback, GraphLoader,
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
    pub(crate) pdg_cache: PdgCache<'tcx>,
    pub(crate) loader: Box<dyn GraphLoader<'tcx> + 'tcx>,
}

#[derive(Debug, TyEncodable, TyDecodable, Clone, Hash, Eq, PartialEq)]
pub enum Error<'tcx> {
    InstanceResolutionFailed {
        function: DefId,
        generics: GenericArgsRef<'tcx>,
        span: Span,
    },
    Impossible,
    FailedLoadingExternalFunction {
        function: DefId,
        span: Span,
    },
    RustcReportedError,
    CrateExistsButItemIsNotFound {
        function: DefId,
    },
    TooManyPredicatesForSynthesizingGenerics {
        function: DefId,
        number: u32,
    },
    BoundVariablesInPredicates {
        function: DefId,
    },
    TraitRefWithBinder {
        function: DefId,
    },
    ConstantInGenerics {
        function: DefId,
    },
    OperandIsNotFunctionType {
        op: String,
    },
    AsyncResolutionErr(AsyncResolutionErr),
}

pub trait EmittableError<'tcx> {
    fn span(&self, _tcx: TyCtxt<'tcx>) -> Option<Span> {
        None
    }
    fn msg(&self, tcx: TyCtxt<'tcx>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;

    fn emit(&self, tcx: TyCtxt<'tcx>) {
        default_emit_error(self, tcx)
    }
}

pub fn default_emit_error<'tcx>(e: &(impl EmittableError<'tcx> + ?Sized), tcx: TyCtxt<'tcx>) {
    struct FmtWithTcx<'tcx, A> {
        tcx: TyCtxt<'tcx>,
        inner: A,
    }
    impl<'tcx, A: EmittableError<'tcx> + ?Sized> Display for FmtWithTcx<'tcx, &'_ A> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.inner.msg(self.tcx, f)
        }
    }

    let msg = format!("{}", FmtWithTcx { tcx, inner: e });
    if let Some(span) = e.span(tcx) {
        tcx.sess.span_err(span, msg);
    } else {
        tcx.sess.err(msg);
    }
}

impl<'tcx> EmittableError<'tcx> for Error<'tcx> {
    fn span(&self, tcx: TyCtxt<'tcx>) -> Option<Span> {
        use Error::*;
        match self {
            AsyncResolutionErr(e) => e.span(tcx),
            InstanceResolutionFailed { span, .. } | FailedLoadingExternalFunction { span, .. } => {
                Some(*span)
            }
            BoundVariablesInPredicates { function }
            | TraitRefWithBinder { function }
            | ConstantInGenerics { function } => Some(tcx.def_span(*function)),
            _ => None,
        }
    }

    fn msg(&self, tcx: TyCtxt, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Error::*;
        match self {
            InstanceResolutionFailed {
                function, generics, ..
            } => write!(
                f,
                "could not resolve instance for {} with generics {generics:?}",
                tcx.def_path_debug_str(*function)
            ),
            Impossible => f.write_str("internal compiler error, this state should be impossible"),
            FailedLoadingExternalFunction { function, .. } => write!(
                f,
                "failed loading external function {}",
                tcx.def_path_debug_str(*function)
            ),
            RustcReportedError => f.write_str("see previously reported errors"),
            CrateExistsButItemIsNotFound { function } => write!(
                f,
                "found a crate for item {}, but could not find a PDG for it",
                tcx.def_path_debug_str(*function)
            ),
            TooManyPredicatesForSynthesizingGenerics { number, .. } => write!(
                f,
                "only one predicate can be synthesized to a `dyn`, found {number}"
            ),
            BoundVariablesInPredicates { .. } => {
                f.write_str("bound variables in predicates are not supported")
            }
            TraitRefWithBinder { .. } => {
                f.write_str("trait refs for `dyn` synthesis cannot have binders")
            }
            ConstantInGenerics { .. } => {
                f.write_str("constants in generics for are not supported for analysis entrypoints")
            }
            OperandIsNotFunctionType { op } => {
                write!(f, "operand {op} is not of function type")
            }
            AsyncResolutionErr(e) => e.msg(tcx, f),
        }
    }
}

impl<'tcx> Error<'tcx> {
    pub fn instance_resolution_failed(
        function: DefId,
        generics: GenericArgsRef<'tcx>,
        span: Span,
    ) -> Self {
        Self::InstanceResolutionFailed {
            function,
            generics,
            span,
        }
    }

    pub fn operand_is_not_function_type(op: &Operand) -> Self {
        Self::OperandIsNotFunctionType {
            op: format!("{op:?}"),
        }
    }
}

impl<'tcx> MemoPdgConstructor<'tcx> {
    /// Initialize the constructor, parameterized over an [`ArtifactLoader`] for
    /// retrieving PDGs of functions from dependencies.
    pub fn new(tcx: TyCtxt<'tcx>, loader: impl GraphLoader<'tcx> + 'tcx) -> Self {
        Self {
            tcx,
            call_change_callback: None,
            dump_mir: false,
            async_info: AsyncInfo::make(tcx).expect("Async functions are not defined"),
            pdg_cache: Default::default(),
            loader: Box::new(loader),
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
    pub fn construct_root<'a>(
        &'a self,
        function: LocalDefId,
    ) -> Result<&'a PartialGraph<'tcx>, Vec<Error<'tcx>>> {
        let generics =
            manufacture_substs_for(self.tcx, function.to_def_id()).map_err(|i| vec![i])?;
        let resolution = try_resolve_function(
            self.tcx,
            function.to_def_id(),
            self.tcx.param_env_reveal_all_normalized(function),
            generics,
        )
        .ok_or_else(|| {
            vec![Error::instance_resolution_failed(
                function.to_def_id(),
                generics,
                self.tcx.def_span(function),
            )]
        })?;
        self.construct_for(resolution)
            .and_then(|f| f.ok_or(vec![Error::Impossible]))
    }

    pub(crate) fn construct_for<'a>(
        &'a self,
        resolution: Instance<'tcx>,
    ) -> Result<Option<&'a PartialGraph<'tcx>>, Vec<Error<'tcx>>> {
        let def_id = resolution.def_id();
        let generics = resolution.args;
        if let Some(local) = def_id.as_local() {
            self.pdg_cache
                .get_maybe_recursive((local, generics), |_| {
                    let g = LocalAnalysis::new(self, resolution).construct_partial()?;
                    g.check_invariants();
                    Ok(g)
                })
                .map(Result::as_ref)
                .transpose()
                .map_err(Clone::clone)
        } else {
            self.loader.load(def_id)
        }
    }

    /// Has a PDG been constructed for this instance before?
    pub fn is_in_cache(&self, resolution: Instance<'tcx>) -> bool {
        if let Some(local) = resolution.def_id().as_local() {
            self.pdg_cache.is_in_cache(&(local, resolution.args))
        } else {
            matches!(self.loader.load(resolution.def_id()), Ok(Some(_)))
        }
    }

    /// Construct a final PDG for this function. Same as
    /// [`Self::construct_root`] this instantiates all generics as `dyn`.
    pub fn construct_graph(
        &self,
        function: LocalDefId,
    ) -> Result<DepGraph<'tcx>, Vec<Error<'tcx>>> {
        let _args = manufacture_substs_for(self.tcx, function.to_def_id())
            .map_err(|_| anyhow!("rustc error"));
        let g = self.construct_root(function)?.to_petgraph();
        Ok(g)
    }
}

pub(crate) struct WithConstructionErrors<'tcx, A> {
    pub(crate) inner: A,
    pub errors: FxHashSet<Error<'tcx>>,
}

impl<'tcx, A> WithConstructionErrors<'tcx, A> {
    pub fn new(inner: A) -> Self {
        Self {
            inner,
            errors: Default::default(),
        }
    }

    pub fn into_result(self) -> Result<A, Vec<Error<'tcx>>> {
        if self.errors.is_empty() {
            Ok(self.inner)
        } else {
            Err(self.errors.into_iter().collect())
        }
    }
}

type DfResults<'mir, 'tcx> = Results<'tcx, DfAna<'mir, 'tcx>>;

type DfAna<'mir, 'tcx> = WithConstructionErrors<'tcx, &'mir LocalAnalysis<'tcx, 'mir>>;

impl<'mir, 'tcx> ResultsVisitor<'mir, 'tcx, DfResults<'mir, 'tcx>>
    for WithConstructionErrors<'tcx, PartialGraph<'tcx>>
{
    type FlowState = <DfAna<'mir, 'tcx> as AnalysisDomain<'tcx>>::Domain;

    fn visit_statement_before_primary_effect(
        &mut self,
        results: &DfResults<'mir, 'tcx>,
        state: &Self::FlowState,
        statement: &'mir rustc_middle::mir::Statement<'tcx>,
        location: Location,
    ) {
        let mut vis = self.inner.modular_mutation_visitor(results, state);

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
        results: &DfResults<'mir, 'tcx>,
        state: &Self::FlowState,
        terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
        if let TerminatorKind::SwitchInt { discr, .. } = &terminator.kind {
            if let Some(place) = discr.place() {
                self.inner.register_mutation(
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

        match self
            .inner
            .handle_as_inline(results, state, terminator, location)
        {
            Ok(false) => (),
            Ok(true) => return,
            Err(e) => self.errors.extend(e),
        }
        trace!("Handling terminator {:?} as not inlined", terminator.kind);
        let mut arg_vis = ModularMutationVisitor::new(
            &results.analysis.inner.place_info,
            move |location, mutation| {
                self.inner.register_mutation(
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

    fn visit_terminator_after_primary_effect(
        &mut self,
        results: &DfResults<'mir, 'tcx>,
        state: &Self::FlowState,
        terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
            let constructor = results.analysis.inner;

            if matches!(
                constructor.determine_call_handling(
                    location,
                    func,
                    args,
                    terminator.source_info.span
                ),
                Ok(Some(CallHandling::Ready { .. }))
            ) {
                return;
            }
        }

        trace!("Handling terminator {:?} as not inlined", terminator.kind);
        let mut arg_vis = ModularMutationVisitor::new(
            &results.analysis.inner.place_info,
            move |location, mutation| {
                self.inner.register_mutation(
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

impl<'tcx> PartialGraph<'tcx> {
    fn modular_mutation_visitor<'a, 'mir>(
        &'a mut self,
        results: &'a DfResults<'mir, 'tcx>,
        state: &'a InstructionState<'tcx>,
    ) -> ModularMutationVisitor<'a, 'tcx, impl FnMut(Location, Mutation<'tcx>) + 'a> {
        ModularMutationVisitor::new(
            &results.analysis.inner.place_info,
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
        )
    }

    /// returns whether we were able to successfully handle this as inline
    fn handle_as_inline<'a>(
        &mut self,
        results: &DfResults<'a, 'tcx>,
        state: &'a InstructionState<'tcx>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) -> Result<bool, Vec<Error<'tcx>>> {
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            return Ok(false);
        };
        let constructor = results.analysis.inner;
        let gloc = GlobalLocation {
            location: location.into(),
            function: constructor.def_id.to_def_id(),
        };

        let Some(handling) = constructor.determine_call_handling(
            location,
            func,
            args,
            terminator.source_info.span,
        )?
        else {
            return Ok(false);
        };

        let (child_descriptor, calling_convention) = match handling {
            CallHandling::Ready {
                calling_convention,
                descriptor,
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
                return Ok(true);
            }
            CallHandling::ApproxAsyncSM(how) => {
                how(
                    constructor,
                    &mut self.modular_mutation_visitor(results, state),
                    args,
                    *destination,
                    location,
                );
                return Ok(true);
            }
        };

        let child_graph = push_call_string_root(child_descriptor, gloc);

        // For each source node CHILD that is parentable to PLACE,
        // add an edge from PLACE -> CHILD.
        trace!("PARENT -> CHILD EDGES:");
        for (child_src, _kind) in child_graph.parentable_srcs() {
            if let Some(parent_place) = calling_convention.translate_to_parent(
                child_src.place,
                constructor.async_info(),
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
        for (child_dst, kind) in child_graph.parentable_dsts() {
            if let Some(parent_place) = calling_convention.translate_to_parent(
                child_dst.place,
                constructor.async_info(),
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
            .insert(CallString::single(gloc), child_descriptor.generics);
        Ok(true)
    }

    fn register_mutation<'a>(
        &mut self,
        results: &DfResults<'a, 'tcx>,
        state: &InstructionState<'tcx>,
        inputs: Inputs<'tcx>,
        mutated: Either<Place<'tcx>, DepNode<'tcx>>,
        location: Location,
        target_use: TargetUse,
    ) {
        trace!("Registering mutation to {mutated:?} with inputs {inputs:?} at {location:?}");
        let constructor = results.analysis.inner;
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
            Either::Left(place) => constructor
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

type PdgCache<'tcx> =
    Rc<Cache<(LocalDefId, GenericArgsRef<'tcx>), Result<PartialGraph<'tcx>, Vec<Error<'tcx>>>>>;

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
