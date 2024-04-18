//! Data-and control flow analyzer and inliner.
//!
//! Analysis starts with the construction of [`SPDGGenerator`] from a
//! [`CollectingVisitor`](crate::discover::CollectingVisitor) and then calling
//! [`analyze`](SPDGGenerator::analyze).

use crate::{
    ann::{Annotation, MarkerAnnotation},
    desc::*,
    discover::FnToAnalyze,
    rust::{hir::def, *},
    stats::{Stats, TimedStat},
    utils::*,
    DefId, HashMap, HashSet, LogLevelConfig, MarkerCtx, Symbol,
};

use std::time::Instant;

use anyhow::Result;
use either::Either;
use itertools::Itertools;
use petgraph::visit::{GraphBase, IntoNodeReferences, NodeRef};
use rustc_span::{FileNameDisplayPreference, Span as RustSpan};

mod graph_converter;
mod inline_judge;

use graph_converter::GraphConverter;

use self::{graph_converter::PlaceInfoCache, inline_judge::InlineJudge};

/// Read-only database of information the analysis needs.
///
/// [`Self::analyze`] serves as the main entrypoint to SPDG generation.
pub struct SPDGGenerator<'tcx> {
    pub inline_judge: InlineJudge<'tcx>,
    pub opts: &'static crate::Args,
    pub tcx: TyCtxt<'tcx>,
    stats: Stats,
    place_info_cache: PlaceInfoCache<'tcx>,
}

impl<'tcx> SPDGGenerator<'tcx> {
    pub fn new(
        marker_ctx: MarkerCtx<'tcx>,
        opts: &'static crate::Args,
        tcx: TyCtxt<'tcx>,
        stats: Stats,
    ) -> Self {
        Self {
            inline_judge: InlineJudge::new(marker_ctx, tcx, opts.anactrl()),
            opts,
            tcx,
            stats,
            place_info_cache: Default::default(),
        }
    }

    pub fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        self.inline_judge.marker_ctx()
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
        let local_def_id = target.def_id.expect_local();

        let converter = GraphConverter::new_with_flowistry(
            self,
            known_def_ids,
            target,
            self.place_info_cache.clone(),
        )?;
        let spdg = converter.make_spdg();

        Ok((local_def_id, spdg))
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
            .filter_map(|l| l.function.to_def_id().as_local())
            .collect::<HashSet<_>>();
        let analyzed_spans = inlined_functions
            .iter()
            .copied()
            // Because we now take the functions seen from the marker context
            // this includes functions where the body is not present (e.g. `dyn`)
            // so if we fail to retrieve the body in that case it is allowed.
            //
            // Prefereably in future we would filter what we get from the marker
            // context better.
            .filter_map(|f| {
                let body = match tcx.body_for_def_id(f) {
                    Ok(b) => Some(b),
                    Err(BodyResolutionError::IsTraitAssocFn(_)) => None,
                    Err(e) => panic!("{e:?}"),
                }?;
                let span = body_span(&body.body);
                Some((f, src_loc_for_span(span, tcx)))
            })
            .collect::<HashMap<_, _>>();

        known_def_ids.extend(inlined_functions.iter().map(|f| f.to_def_id()));

        let type_info = self.collect_type_info();
        known_def_ids.extend(type_info.keys());
        let def_info = known_def_ids
            .iter()
            .map(|id| (*id, def_info_for_item(*id, self.marker_ctx(), tcx)))
            .collect();

        let dedup_locs = analyzed_spans.values().map(Span::line_len).sum();
        let dedup_functions = analyzed_spans.len() as u32;

        let (seen_locs, seen_functions) = if self.opts.anactrl().inlining_depth().is_adaptive() {
            let mut total_functions = inlined_functions;
            let mctx = self.marker_ctx();
            total_functions.extend(
                mctx.functions_seen()
                    .into_iter()
                    .map(|f| f.def_id())
                    .filter(|f| !mctx.is_marked(f))
                    .filter_map(|f| f.as_local()),
            );
            let mut seen_functions = 0;
            let locs = total_functions
                .into_iter()
                .filter_map(|f| Some(body_span(&tcx.body_for_def_id(f).ok()?.body)))
                .map(|span| {
                    seen_functions += 1;
                    let (_, start_line, _, end_line, _) =
                        tcx.sess.source_map().span_to_location_info(span);
                    end_line - start_line + 1
                })
                .sum::<usize>() as u32;
            (locs, seen_functions)
        } else {
            (dedup_locs, dedup_functions)
        };

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
            analyzed_spans,
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
                let body = &self.tcx.body_for_def_id(i.function).unwrap().body;

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
    let file_path = source_file
        .expect("could not find source file")
        .name
        .display(FileNameDisplayPreference::Local)
        .to_string();
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
