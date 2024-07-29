//! Data-and control flow analyzer and inliner.
//!
//! Analysis starts with the construction of [`SPDGGenerator`] from a
//! [`CollectingVisitor`](crate::discover::CollectingVisitor) and then calling
//! [`analyze`](SPDGGenerator::analyze).

use crate::{
    ann::{Annotation, MarkerAnnotation},
    desc::*,
    discover::FnToAnalyze,
    stats::{Stats, TimedStat},
    utils::*,
    HashMap, HashSet, LogLevelConfig, MarkerCtx,
};

use std::{rc::Rc, time::Instant};

use anyhow::Result;
use either::Either;
use flowistry::mir::FlowistryInput;
use flowistry_pdg_construction::{
    body_cache::BodyCache, CallChangeCallback, CallChanges, CallInfo, MemoPdgConstructor, SkipCall,
};
use itertools::Itertools;
use petgraph::visit::GraphBase;

use rustc_hir::{self as hir, def, def_id::DefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::{FileNameDisplayPreference, Span as RustSpan, Symbol};

mod graph_converter;
mod inline_judge;

use graph_converter::GraphConverter;

pub use self::inline_judge::InlineJudge;

/// Read-only database of information the analysis needs.
///
/// [`Self::analyze`] serves as the main entrypoint to SPDG generation.
pub struct SPDGGenerator<'tcx> {
    pub opts: &'static crate::Args,
    pub tcx: TyCtxt<'tcx>,
    stats: Stats,
    pdg_constructor: MemoPdgConstructor<'tcx>,
    judge: Rc<InlineJudge<'tcx>>,
}

impl<'tcx> SPDGGenerator<'tcx> {
    pub fn new(
        inline_judge: InlineJudge<'tcx>,
        opts: &'static crate::Args,
        tcx: TyCtxt<'tcx>,
        body_cache: Rc<BodyCache<'tcx>>,
        stats: Stats,
    ) -> Self {
        let judge = Rc::new(inline_judge);
        let mut pdg_constructor = MemoPdgConstructor::new_with_cache(tcx, body_cache);
        pdg_constructor
            .with_call_change_callback(MyCallback {
                judge: judge.clone(),
                tcx,
            })
            .with_dump_mir(opts.dbg().dump_mir());
        Self {
            pdg_constructor,
            opts,
            tcx,
            stats,
            judge,
        }
    }

    pub fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        self.judge.marker_ctx()
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
        info!("Handling target {}", self.tcx.def_path_str(target.def_id));
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
    pub fn analyze(&mut self, targets: Vec<FnToAnalyze>) -> Result<ProgramDescription> {
        if let LogLevelConfig::Targeted(s) = self.opts.direct_debug() {
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
                with_reset_level_if_target(self.opts, target_name, || {
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
    ) -> ProgramDescription {
        let tcx = self.tcx;

        let instruction_info = self.collect_instruction_info(&controllers);

        let inlined_functions = instruction_info
            .keys()
            .map(|l| l.function)
            .collect::<HashSet<_>>();

        known_def_ids.extend(&inlined_functions);

        let type_info = self.collect_type_info();
        known_def_ids.extend(type_info.keys());
        let def_info = known_def_ids
            .iter()
            .map(|id| (*id, def_info_for_item(*id, self.marker_ctx(), tcx)))
            .collect();

        let dedup_locs = 0;
        let dedup_functions = 0;
        let seen_locs = 0;
        let seen_functions = 0;

        type_info_sanity_check(&controllers, &type_info);
        ProgramDescription {
            type_info,
            instruction_info,
            controllers,
            def_info,
            marker_annotation_count: self
                .marker_ctx()
                .all_annotations()
                .filter_map(|m| m.1.either(Annotation::as_marker, Some))
                .count() as u32,
            rustc_time: self.stats.get_timed(TimedStat::Rustc),
            dedup_locs,
            dedup_functions,
            seen_functions,
            seen_locs,
            analyzed_spans: Default::default(),
        }
    }

    /// Create an [`InstructionInfo`] record for each [`GlobalLocation`]
    /// mentioned in the controllers.
    fn collect_instruction_info(
        &self,
        controllers: &HashMap<Endpoint, SPDG>,
    ) -> HashMap<GlobalLocation, InstructionInfo> {
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
                let body = self
                    .pdg_constructor
                    .body_for_def_id(i.function)
                    .unwrap()
                    .body();

                let (kind, description) = match i.location {
                    RichLocation::End => (InstructionKind::Return, "start".to_owned()),
                    RichLocation::Start => (InstructionKind::Start, "end".to_owned()),
                    RichLocation::Location(loc) => match body.stmt_at(loc) {
                        crate::Either::Right(term) => {
                            let kind = if let Ok((id, ..)) = term.as_fn_and_args(self.tcx) {
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
                        self.tcx
                            .sess
                            .source_map()
                            .stmt_span(expanded_span, body.span)
                    }
                    RichLocation::Start | RichLocation::End => self.tcx.def_span(i.function),
                };
                (
                    i,
                    InstructionInfo {
                        kind,
                        span: src_loc_for_span(rust_span, self.tcx),
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
            .filter(|(id, _)| def_kind_for_item(*id, self.tcx).is_type())
            .into_grouping_map()
            .fold_with(
                |id, _| (format!("{id:?}"), vec![], vec![]),
                |mut desc, _, ann| {
                    match ann {
                        Either::Right(MarkerAnnotation { refinement, marker })
                        | Either::Left(Annotation::Marker(MarkerAnnotation {
                            refinement,
                            marker,
                        })) => {
                            assert!(refinement.on_self());
                            desc.2.push(*marker)
                        }
                        Either::Left(Annotation::OType(id)) => desc.1.push(*id),
                        _ => panic!("Unexpected type of annotation {ann:?}"),
                    }
                    desc
                },
            )
            .into_iter()
            .map(|(k, (rendering, otypes, markers))| {
                (
                    k,
                    TypeDescription {
                        rendering,
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

impl<'tcx> CallChangeCallback<'tcx> for MyCallback<'tcx> {
    fn on_inline(&self, info: CallInfo<'tcx>) -> CallChanges {
        let mut changes = CallChanges::default();

        let mut skip = true;

        if is_virtual(self.tcx, info.callee.def_id()) {
            self.tcx.sess.span_warn(
                self.tcx.def_span(info.callee.def_id()),
                "Skipping analysis of unresolvable trait method.",
            );
        } else if self.judge.should_inline(&info) {
            skip = false;
        };

        if skip {
            changes = changes.with_skip(SkipCall::Skip);
        } else {
            // record_inlining(
            //     &self.stat_wrap,
            //     self.tcx,
            //     info.callee.def_id().expect_local(),
            //     info.is_cached,
            // )
        }
        changes
    }

    // fn on_inline_miss(
    //     &self,
    //     resolution: FnResolution<'tcx>,
    //     loc: Location,
    //     parent: FnResolution<'tcx>,
    //     call_string: Option<CallString>,
    //     reason: InlineMissReason,
    // ) {
    //     let body = self
    //         .tcx
    //         .body_for_def_id(parent.def_id().expect_local())
    //         .unwrap();
    //     let span = body
    //         .body
    //         .stmt_at(loc)
    //         .either(|s| s.source_info.span, |t| t.source_info.span);
    //     let markers_reachable = self.judge.marker_ctx().get_reachable_markers(resolution);
    //     self.tcx.sess.span_err(
    //         span,
    //         format!(
    //             "Could not inline this function call in {:?}, at {} because {reason:?}. {}",
    //             parent.def_id(),
    //             call_string.map_or("root".to_owned(), |c| c.to_string()),
    //             Print(|f| if markers_reachable.is_empty() {
    //                 f.write_str("No markers are reachable")
    //             } else {
    //                 f.write_str("Markers ")?;
    //                 write_sep(f, ", ", markers_reachable.iter(), Display::fmt)?;
    //                 f.write_str(" are reachable")
    //             })
    //         ),
    //     );
    // }
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
