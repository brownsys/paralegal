//! Data-and control flow analyzer and inliner.
//!
//! Analysis starts with the construction of [`SPDGGenerator`] from a
//! [`CollectingVisitor`](crate::discover::CollectingVisitor) and then calling
//! [`analyze`](SPDGGenerator::analyze).

use crate::{
    ann::{Annotation, MarkerAnnotation},
    args::Stub,
    desc::*,
    discover::FnToAnalyze,
    stats::{Stats, TimedStat},
    utils::*,
    DumpStats, HashMap, HashSet, LogLevelConfig, MarkerCtx, Pctx, INTERMEDIATE_STAT_EXT,
};

use std::{fs::File, io::BufReader, rc::Rc, time::Instant};

use anyhow::Result;
use either::Either;
use flowistry::mir::FlowistryInput;
use flowistry_pdg_construction::{
    body_cache::{local_or_remote_paths, BodyCache},
    calling_convention::CallingConvention,
    utils::is_async,
    CallChangeCallback, CallChanges, CallInfo, InlineMissReason, MemoPdgConstructor, SkipCall,
};
use inline_judge::InlineJudgement;
use itertools::Itertools;
use petgraph::visit::GraphBase;

use rustc_hir::{
    self as hir, def,
    def_id::{DefId, LOCAL_CRATE},
};
use rustc_middle::{
    mir::{Location, Operand},
    ty::{Instance, ParamEnv, TyCtxt},
};
use rustc_span::{ErrorGuaranteed, FileNameDisplayPreference, Span as RustSpan, Symbol};

mod graph_converter;
mod inline_judge;

use graph_converter::GraphConverter;
use std::time::Duration;

pub use self::inline_judge::InlineJudge;

/// Read-only database of information the analysis needs.
///
/// [`Self::analyze`] serves as the main entrypoint to SPDG generation.
pub struct SPDGGenerator<'tcx> {
    ctx: Pctx<'tcx>,
    stats: Stats,
    pdg_constructor: MemoPdgConstructor<'tcx>,
    judge: Rc<InlineJudge<'tcx>>,
    functions_to_analyze: Vec<FnToAnalyze>,
}

impl<'tcx> SPDGGenerator<'tcx> {
    pub fn new(
        ctx: Pctx<'tcx>,
        inline_judge: InlineJudge<'tcx>,
        stats: Stats,
        functions_to_analyze: Vec<FnToAnalyze>,
    ) -> Self {
        let judge = Rc::new(inline_judge);
        let mut pdg_constructor =
            MemoPdgConstructor::new_with_cache(ctx.tcx(), ctx.body_cache().clone());
        pdg_constructor
            .with_call_change_callback(MyCallback {
                judge: judge.clone(),
                tcx: ctx.tcx(),
            })
            .with_dump_mir(ctx.opts().dbg().dump_mir())
            .with_relaxed(ctx.opts().relaxed())
            .with_disable_cache(!ctx.opts().anactrl().pdg_cache());
        Self {
            pdg_constructor,
            ctx,
            stats,
            judge,
            functions_to_analyze,
        }
    }

    pub fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        self.ctx.marker_ctx()
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx()
    }

    /// Perform the analysis for one `#[paralegal_flow::analyze]` annotated function and
    /// return the representation suitable for emitting into Forge.
    ///
    /// Main work for a single target is performed by [`GraphConverter`].
    fn handle_target(
        &mut self,
        //_hash_verifications: &mut HashVerifications,
        target: &FnToAnalyze,
        known_def_ids: &mut impl Extend<DefId>,
    ) -> Result<(Endpoint, SPDG)> {
        info!(
            "Handling target {}",
            self.ctx.tcx().def_path_str(target.def_id)
        );
        let local_def_id = target.def_id;

        let converter = GraphConverter::new_with_flowistry(self, known_def_ids, target)?;
        let spdg = converter.make_spdg();

        Ok((local_def_id.to_def_id(), spdg))
    }

    /// Main analysis driver. Essentially just calls [`Self::handle_target`]
    /// once for every function in `self.functions_to_analyze` after doing some
    /// other setup necessary for the flow graph creation.
    ///
    /// Should only be called after the visit.
    pub fn analyze(&mut self) -> Result<(ProgramDescription, AnalyzerStats)> {
        let targets = std::mem::take(&mut self.functions_to_analyze);
        if let LogLevelConfig::Targeted(s) = self.ctx.opts().direct_debug() {
            assert!(
                targets.iter().any(|target| target.name().as_str() == s),
                "Debug output option specified a specific target '{s}', but no such target was found in [{}]",
                Print(|f: &mut std::fmt::Formatter<'_>| {
                    write_sep(f, ", ", targets.iter(), |t, f| {
                        f.write_str(t.name().as_str())
                    })
                })
            )
        }

        let mut known_def_ids = HashSet::new();

        targets
            .iter()
            .map(|desc| {
                let target_name = desc.name();
                with_reset_level_if_target(self.ctx.opts(), target_name, || {
                    self.handle_target(
                        //hash_verifications,
                        desc,
                        &mut known_def_ids,
                    )
                })
            })
            .collect::<Result<HashMap<Endpoint, SPDG>>>()
            .map(|controllers| {
                let start = Instant::now();
                let desc = self.make_program_description(controllers, known_def_ids, &targets);
                self.stats
                    .record_timed(TimedStat::Conversion, start.elapsed());
                desc
            })
    }

    /// Given the PDGs and a record of all [`DefId`]s we've seen, compile
    /// auxillary information the policies will need into the artifact to be
    /// emitted.
    fn make_program_description(
        &self,
        controllers: HashMap<Endpoint, SPDG>,
        mut known_def_ids: HashSet<DefId>,
        _targets: &[FnToAnalyze],
    ) -> (ProgramDescription, AnalyzerStats) {
        let tcx = self.ctx.tcx();

        let instruction_info = self.collect_instruction_info(&controllers);

        let called_functions = instruction_info
            .keys()
            .map(|l| l.function)
            .collect::<HashSet<_>>();

        known_def_ids.extend(&called_functions);

        let type_info = self.collect_type_info();
        known_def_ids.extend(type_info.keys());
        let def_info = known_def_ids
            .iter()
            .map(|id| (*id, def_info_for_item(*id, self.marker_ctx(), tcx)))
            .collect();

        type_info_sanity_check(&controllers, &type_info);

        let (stats, analyzed_spans) = self.collect_stats_and_analyzed_spans();

        (
            ProgramDescription {
                type_info,
                instruction_info,
                controllers,
                def_info,
                analyzed_spans,
            },
            stats,
        )
    }

    fn collect_stats_and_analyzed_spans(&self) -> (AnalyzerStats, AnalyzedSpans) {
        let tcx = self.ctx.tcx();

        // In this we don't have to filter out async functions. They are already
        // not in it. For the top-level (target) an async function immediately
        // redirects to its closure and never inserts the parent DefId into the
        // map. For called async functions we skip inlining and therefore also
        // do not insert the DefId into the map.
        let inlined_functions = self
            .pdg_constructor
            .pdg_cache
            .borrow()
            .keys()
            .map(|k| k.def.def_id())
            .collect::<HashSet<_>>();

        let mut seen_locs = 0;
        let mut seen_functions = 0;
        let mut pdg_locs = 0;
        let mut pdg_functions = 0;

        let mctx = self.marker_ctx();

        let analyzed_functions = mctx
            .functions_seen()
            .into_iter()
            .map(|f| f.def_id())
            // Async functions always show up twice, once as the function
            // itself, once as the generator. Here we filter out one of those
            // (the function)
            .filter(|d| !is_async(tcx, *d))
            .filter(|f| !mctx.is_marked(f))
            // It's annoying I have to do this merge here, but what the marker
            // context sees doesn't contain the targets and not just that but
            // also if those targets are async, then their closures are also not
            // contained and lastly if we're not doing adaptive depth then we
            // need to use the inlined functions anyway so this is just easier.
            .chain(inlined_functions.iter().copied())
            .collect::<HashSet<_>>();

        let analyzed_spans = analyzed_functions
            .into_iter()
            .filter_map(|f| {
                if tcx.is_constructor(f) {
                    return None;
                }
                let body = self.pdg_constructor.body_for_def_id(f);
                let span = body_span(tcx, body.body());
                let pspan = src_loc_for_span(span, tcx);
                assert!(
                    pspan.start.line <= pspan.end.line,
                    "Weird span for {f:?}: {pspan:?}. It was created from {span:?}"
                );
                let l = pspan.line_len();
                assert!(l < 5000, "Span for {f:?} is {l} lines long ({span:?})");

                seen_locs += pspan.line_len();
                seen_functions += 1;

                let handling = if inlined_functions.contains(&f) {
                    pdg_locs += pspan.line_len();
                    pdg_functions += 1;
                    FunctionHandling::PDG
                } else {
                    FunctionHandling::Elided
                };

                Some((f, (pspan, handling)))
            })
            .collect::<AnalyzedSpans>();

        let prior_stats = self.get_prior_stats();

        // A few notes on these stats. We calculate most of them here, because
        // this is where we easily have access to the information. For example
        // the included crates, the paths where the intermediate stats are
        // located and the marker annotations.
        //
        // However some pieces of information we don't have and that is how long
        // *this* run of the analyzer took in total and how long serialziation
        // took, but we do want to add that to the stats. As a workaround we set
        // "self_time" and "serialization_time" to 0 and "total_time" to the
        // accumulated intermediate analyis time. Then, after the serialization
        // and whatever teardown rustc wants to do is finished we set
        // "self_time" and increment "total_time". See lib.rs for that.
        let stats = AnalyzerStats {
            marker_annotation_count: mctx
                .all_annotations()
                .filter_map(|m| m.1.either(Annotation::as_marker, Some))
                .count() as u32,
            rustc_time: self.stats.get_timed(TimedStat::Rustc),
            pdg_functions,
            pdg_locs,
            seen_functions,
            seen_locs,
            self_time: Duration::ZERO,
            dep_time: prior_stats.total_time,
            tycheck_time: prior_stats.tycheck_time + self.pdg_constructor.body_cache().timer(),
            dump_time: prior_stats.dump_time,
            serialization_time: Duration::ZERO,
        };

        (stats, analyzed_spans)
    }

    fn get_prior_stats(&self) -> DumpStats {
        self.ctx
            .opts()
            .anactrl()
            .included_crates(self.ctx.tcx())
            .filter(|c| *c != LOCAL_CRATE)
            .map(|c| {
                let paths = local_or_remote_paths(c, self.ctx.tcx(), INTERMEDIATE_STAT_EXT);

                let path = paths.iter().find(|p| p.exists()).unwrap_or_else(|| {
                    panic!("No stats path found for included crate {c:?}, searched {paths:?}")
                });
                let rdr = BufReader::new(File::open(path).unwrap());
                serde_json::from_reader(rdr).unwrap()
            })
            .fold(DumpStats::zero(), |s, o| s.add(&o))
    }

    /// Create an [`InstructionInfo`] record for each [`GlobalLocation`]
    /// mentioned in the controllers.
    fn collect_instruction_info(
        &self,
        controllers: &HashMap<Endpoint, SPDG>,
    ) -> HashMap<GlobalLocation, InstructionInfo> {
        let tcx = self.ctx.tcx();
        let all_instructions = controllers
            .values()
            .flat_map(|v| {
                v.graph
                    .node_weights()
                    .flat_map(|n| n.at.iter())
                    .chain(v.graph.edge_weights().flat_map(|e| e.at.iter()))
            })
            .collect::<HashSet<_>>();
        all_instructions
            .into_iter()
            .map(|i| {
                let body = self.pdg_constructor.body_for_def_id(i.function).body();

                let (kind, description) = match i.location {
                    RichLocation::End => (InstructionKind::Return, "start".to_owned()),
                    RichLocation::Start => (InstructionKind::Start, "end".to_owned()),
                    RichLocation::Location(loc) => match body.stmt_at(loc) {
                        crate::Either::Right(term) => {
                            let kind = if let Ok((id, ..)) = term.as_fn_and_args(tcx) {
                                InstructionKind::FunctionCall(FunctionCallInfo {
                                    id,
                                    is_inlined: id.is_local(),
                                })
                            } else {
                                InstructionKind::Terminator
                            };
                            (kind, format!("{:?}", term.kind))
                        }
                        crate::Either::Left(stmt) => {
                            (InstructionKind::Statement, format!("{:?}", stmt.kind))
                        }
                    },
                };
                let rust_span = match i.location {
                    RichLocation::Location(loc) => {
                        let expanded_span = match body.stmt_at(loc) {
                            crate::Either::Right(term) => term.source_info.span,
                            crate::Either::Left(stmt) => stmt.source_info.span,
                        };
                        tcx.sess.source_map().stmt_span(expanded_span, body.span)
                    }
                    RichLocation::Start | RichLocation::End => tcx.def_span(i.function),
                };
                (
                    i,
                    InstructionInfo {
                        kind,
                        span: src_loc_for_span(rust_span, tcx),
                        description: Identifier::new_intern(&description),
                    },
                )
            })
            .collect()
    }

    /// Create a [`TypeDescription`] record for each marked type that as
    /// mentioned in the PDG.
    fn collect_type_info(&self) -> TypeInfoMap {
        self.marker_ctx()
            .all_annotations()
            .filter(|(id, _)| def_kind_for_item(*id, self.ctx.tcx()).is_type())
            .into_grouping_map()
            .fold_with(
                |id, _| (*id, vec![], vec![]),
                |mut desc, _, ann| {
                    match ann {
                        Either::Right(MarkerAnnotation { refinement, marker })
                        | Either::Left(Annotation::Marker(MarkerAnnotation {
                            refinement,
                            marker,
                        })) => {
                            assert!(refinement.on_self(), "Cannot refine a marker on a type (tried assigning refinement {refinement} to {:?})", desc.0);
                            desc.2.push(*marker)
                        }
                        Either::Left(Annotation::OType(id)) => desc.1.push(*id),
                        _ => panic!("Unexpected type of annotation {ann:?}"),
                    }
                    desc
                },
            )
            .into_iter()
            .map(|(k, (_, otypes, markers))| {
                (
                    k,
                    TypeDescription {
                        rendering: format!("{k:?}"),
                        otypes: otypes.into(),
                        markers,
                    },
                )
            })
            .collect()
    }
}

fn src_loc_for_span(span: RustSpan, tcx: TyCtxt) -> Span {
    let (source_file, start_line, start_col, end_line, end_col) =
        tcx.sess.source_map().span_to_location_info(span);
    let file_path = source_file.map_or_else(
        || "<unknown>".to_string(),
        |f| f.name.display(FileNameDisplayPreference::Local).to_string(),
    );
    let abs_file_path = if !file_path.starts_with('/') {
        std::env::current_dir()
            .expect("failed to obtain current working directory")
            .join(&file_path)
    } else {
        std::path::PathBuf::from(&file_path)
    };
    let src_info = SourceFileInfo {
        file_path,
        abs_file_path,
    };
    Span {
        source_file: src_info.intern(),
        start: SpanCoord {
            line: start_line as u32,
            col: start_col as u32,
        },
        end: SpanCoord {
            line: end_line as u32,
            col: end_col as u32,
        },
    }
}

fn default_index() -> <SPDGImpl as GraphBase>::NodeId {
    <SPDGImpl as GraphBase>::NodeId::end()
}

/// Checks the invariant that [`SPDGGenerator::collect_type_info`] should
/// produce a map that is a superset of the types found in all the `types` maps
/// on [`SPDG`].
fn type_info_sanity_check(controllers: &ControllerMap, types: &TypeInfoMap) {
    controllers
        .values()
        .flat_map(|spdg| spdg.type_assigns.values())
        .flat_map(|types| types.0.iter())
        .for_each(|t| {
            assert!(
                types.contains_key(t),
                "Invariant broken: Type {t:?} is not present in type map"
            );
        })
}

fn def_kind_for_item(id: DefId, tcx: TyCtxt) -> DefKind {
    match tcx.def_kind(id) {
        def::DefKind::Closure => DefKind::Closure,
        def::DefKind::Generator => DefKind::Generator,
        kind if kind.is_fn_like() => DefKind::Fn,
        def::DefKind::Struct
        | def::DefKind::AssocTy
        | def::DefKind::OpaqueTy
        | def::DefKind::TyAlias { .. }
        | def::DefKind::Enum => DefKind::Type,
        def::DefKind::Ctor { .. } => DefKind::Ctor,
        kind => unreachable!("{} ({:?})", tcx.def_path_debug_str(id), kind),
    }
}

fn path_for_item(id: DefId, tcx: TyCtxt) -> Box<[Identifier]> {
    let def_path = tcx.def_path(id);
    std::iter::once(Identifier::new(tcx.crate_name(def_path.krate)))
        .chain(def_path.data.iter().filter_map(|segment| {
            use hir::definitions::DefPathDataName::*;
            match segment.data.name() {
                Named(sym) => Some(Identifier::new(sym)),
                Anon { .. } => None,
            }
        }))
        .collect()
}

fn def_info_for_item(id: DefId, markers: &MarkerCtx, tcx: TyCtxt) -> DefInfo {
    let name = crate::utils::identifier_for_item(tcx, id);
    let kind = def_kind_for_item(id, tcx);
    DefInfo {
        name,
        path: path_for_item(id, tcx),
        kind,
        src_info: src_loc_for_span(tcx.def_span(id), tcx),
        markers: markers
            .combined_markers(id)
            .cloned()
            .map(|ann| paralegal_spdg::MarkerAnnotation {
                marker: ann.marker,
                on_return: ann.refinement.on_return(),
                on_argument: ann.refinement.on_argument(),
            })
            .collect(),
    }
}

/// A higher order function that increases the logging level if the `target`
/// matches the one selected with the `debug` flag on the command line (and
/// reset it afterward).
fn with_reset_level_if_target<R, F: FnOnce() -> R>(opts: &crate::Args, target: Symbol, f: F) -> R {
    if matches!(opts.direct_debug(), LogLevelConfig::Targeted(s) if target.as_str() == s) {
        with_temporary_logging_level(opts.verbosity(), f)
    } else {
        f()
    }
}

struct MyCallback<'tcx> {
    judge: Rc<InlineJudge<'tcx>>,
    // stat_wrap: StatStracker,
    tcx: TyCtxt<'tcx>,
}

impl Stub {
    pub fn resolve_alternate_instance<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        function: Instance<'tcx>,
        param_env: ParamEnv<'tcx>,
        at: RustSpan,
    ) -> Result<Instance<'tcx>, ErrorGuaranteed> {
        match self {
            Stub::SubClosure { generic_name } | Stub::SubFuture { generic_name } => {
                let name = Symbol::intern(generic_name);
                let generics = tcx.generics_of(function.def_id());
                let Some(param_index) = (0..generics.count()).find(|&idx| {
                    let param = generics.param_at(idx, tcx);
                    param.name == name
                }) else {
                    return Err(tcx.sess.span_err(
                        at,
                        format!("Function has no parameter named {generic_name}"),
                    ));
                };
                let ty = function.args[param_index].expect_ty();
                let (def_id, args) =
                    flowistry_pdg_construction::utils::type_as_fn(tcx, ty).unwrap();
                Ok(Instance::resolve(tcx, param_env, def_id, args)
                    .unwrap()
                    .unwrap())
            }
        }
    }

    fn indirect_required(
        &self,
        tcx: TyCtxt,
        def_id: DefId,
        at: RustSpan,
    ) -> Result<bool, ErrorGuaranteed> {
        let bool = match self {
            Stub::SubClosure { .. } => {
                use rustc_hir::def::DefKind;
                match tcx.def_kind(def_id) {
                    DefKind::Closure => true,
                    DefKind::Fn => false,
                    kind => {
                        return Err(tcx.sess.span_err(
                            at,
                            format!("Expected `fn` or `closure` def kind, got {kind:?}"),
                        ))
                    }
                }
            }
            Stub::SubFuture { .. } => {
                assert!(tcx.generator_is_async(def_id));
                true
            }
        };
        Ok(bool)
    }

    /// Performs the effects of this model on the provided function.
    ///
    /// `function` is what was to be called but for which a stub exists,
    /// `arguments` are the arguments to that call.
    ///
    /// Returns a new instance to call instead and how it should be called.
    pub fn apply<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        function: Instance<'tcx>,
        param_env: ParamEnv<'tcx>,
        arguments: &[Operand<'tcx>],
        at: RustSpan,
    ) -> Result<(Instance<'tcx>, CallingConvention<'tcx>), ErrorGuaranteed> {
        let instance = self.resolve_alternate_instance(tcx, function, param_env, at)?;
        let def_id = instance.def_id();

        let expect_indirect = self.indirect_required(tcx, def_id, at)?;
        let poll = tcx.lang_items().poll();
        let calling_convention = if expect_indirect {
            let clj = match arguments {
                [clj] => clj,
                [gen, _]
                    if tcx.def_kind(function.def_id()) == hir::def::DefKind::AssocFn
                        && tcx.associated_item(function.def_id()).trait_item_def_id == poll =>
                {
                    gen
                }
                _ => {
                    return Err(tcx.sess.span_err(
                        at,
                        format!(
                            "this function ({:?}) should have only one argument but it has {}",
                            function.def_id(),
                            arguments.len()
                        ),
                    ))
                }
            };
            CallingConvention::Indirect {
                shim: None,
                closure_arg: clj.clone(),
                // This is incorrect, but we only support
                // non-argument closures at the moment so this
                // will never be used.
                tupled_arguments: clj.clone(),
            }
        } else {
            CallingConvention::Direct(arguments.into())
        };
        Ok((instance, calling_convention))
    }
}

impl<'tcx> CallChangeCallback<'tcx> for MyCallback<'tcx> {
    fn on_inline(&self, info: CallInfo<'tcx, '_>) -> CallChanges<'tcx> {
        let changes = CallChanges::default();

        let judgement = self.judge.should_inline(&info);

        debug!("Judgement for {:?}: {judgement}", info.callee.def_id(),);

        let skip = match judgement {
            InlineJudgement::AbstractViaType(_) => SkipCall::Skip,
            InlineJudgement::UseStub(model) => {
                if let Ok((instance, calling_convention)) = model.apply(
                    self.tcx,
                    info.callee,
                    info.param_env,
                    info.arguments,
                    info.span,
                ) {
                    SkipCall::Replace {
                        instance,
                        calling_convention,
                    }
                } else {
                    SkipCall::Skip
                }
            }
            InlineJudgement::Inline => SkipCall::NoSkip,
        };
        changes.with_skip(skip)
    }
    fn on_inline_miss(
        &self,
        resolution: Instance<'tcx>,
        param_env: ParamEnv<'tcx>,
        _loc: Location,
        _parent: Instance<'tcx>,
        reason: InlineMissReason,
        call_span: rustc_span::Span,
    ) {
        self.judge.ensure_is_safe_to_approximate(
            param_env,
            resolution,
            call_span,
            false,
            match reason {
                InlineMissReason::Async(_) => "async",
                InlineMissReason::TraitMethod => "virtual trait method",
            },
        );
    }
}

//type StatStracker = Rc<RefCell<(SPDGStats, HashSet<LocalDefId>)>>;

// fn record_inlining(tracker: &StatStracker, tcx: TyCtxt<'_>, def_id: LocalDefId, is_in_cache: bool) {
//     let mut borrow = tracker.borrow_mut();
//     let (stats, loc_set) = &mut *borrow;
//     stats.inlinings_performed += 1;
//     let is_new = loc_set.insert(def_id);

//     if !is_new || is_in_cache {
//         return;
//     }

//     let src_map = tcx.sess.source_map();
//     let span = body_span(&tcx.body_for_def_id(def_id).unwrap().body);
//     let (_, start_line, _, end_line, _) = src_map.span_to_location_info(span);
//     let body_lines = (end_line - start_line + 1) as u32;
//     if is_new {
//         stats.unique_functions += 1;
//         stats.unique_locs += body_lines;
//     }
//     if !is_in_cache {
//         stats.analyzed_functions += 1;
//         stats.analyzed_locs += body_lines;
//     }
// }
