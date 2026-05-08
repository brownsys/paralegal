//! [`SPDGGenerator`] — the top-level driver that turns the set of
//! `#[paralegal_flow::analyze]`-annotated functions into a [`ProgramDescription`].
//!
//! The flow is: build (or reuse) a [`MemoPdgConstructor`], assemble one SPDG
//! per target via [`assemble_pdg`], then collect the auxiliary metadata
//! (instruction info, type info, def info, analyzer stats) the policies will
//! need.

use std::{fs::File, io::BufReader, rc::Rc, time::Duration, time::Instant};

use anyhow::Result;
use itertools::Itertools;
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_middle::ty::TyCtxt;
use tracing::info;

use crate::{
    DumpStats, HashMap, HashSet, INTERMEDIATE_STAT_EXT, MarkerCtx, Pctx,
    ann::{Annotation, MarkerAnnotation},
    desc::*,
    discover::FnToAnalyze,
    mir::FlowistryInput,
    source_access::local_or_remote_paths,
    stats::{Stats, TimedStat},
    utils::*,
};

use super::{
    InlineJudge, MemoPdgConstructor, assemble_pdg,
    callback_adapter::MyCallback,
    def_info::{
        def_info_for_item, def_kind_for_item, dirty_try_resolve_func_id, src_loc_for_span,
        type_info_sanity_check,
    },
    inline_judge::K,
};

/// Read-only database of information the analysis needs.
///
/// [`Self::analyze`] serves as the main entrypoint to SPDG generation.
pub struct SPDGGenerator<'tcx> {
    ctx: Pctx<'tcx>,
    stats: Stats,
    pdg_constructor: MemoPdgConstructor<'tcx, K>,
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
            .with_call_change_callback(MyCallback::new(judge, ctx.tcx()))
            .with_dump_mir(ctx.opts().dbg().dump_mir())
            .with_relaxed(ctx.opts().relaxed())
            .with_disable_cache(!ctx.opts().anactrl().pdg_cache());
        Self {
            pdg_constructor,
            ctx,
            stats,
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
    fn handle_target(
        &mut self,
        target: &FnToAnalyze,
        known_def_ids: &mut FxHashSet<DefId>,
    ) -> Result<(Endpoint, SPDG)> {
        info!(
            "Handling target {}",
            self.ctx.tcx().def_path_str(target.def_id)
        );
        let local_def_id = target.def_id;

        let pdg = assemble_pdg(
            &self.ctx,
            &self.pdg_constructor,
            known_def_ids,
            target.def_id.to_def_id(),
        );

        Ok((local_def_id.to_def_id(), pdg))
    }

    /// Main analysis driver. Essentially just calls [`Self::handle_target`]
    /// once for every function in `self.functions_to_analyze` after doing some
    /// other setup necessary for the flow graph creation.
    ///
    /// Should only be called after the visit.
    pub fn analyze(&mut self) -> Result<(ProgramDescription, AnalyzerStats)> {
        let targets = std::mem::take(&mut self.functions_to_analyze);

        let mut known_def_ids = FxHashSet::default();

        targets
            .iter()
            .map(|desc| self.handle_target(desc, &mut known_def_ids))
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
        mut known_def_ids: FxHashSet<DefId>,
        _targets: &[FnToAnalyze],
    ) -> (ProgramDescription, AnalyzerStats) {
        let tcx = self.ctx.tcx();

        let instruction_info = self.collect_instruction_info(&controllers, &mut known_def_ids);

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
            marker_annotation_count: mctx.marker_count() as u32,
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
                    panic!(
                        "No stats path found for included crate {}, searched {paths:?}",
                        self.tcx().crate_name(c)
                    )
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
        known_def_ids: &mut impl Extend<DefId>,
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
                            let kind = if let Some(id) = dirty_try_resolve_func_id(tcx, term) {
                                known_def_ids.extend([id]);
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
                        let expanded_span = body.source_info(loc).span;
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
                        | Annotation::Marker(MarkerAnnotation {
                            refinement,
                            marker,
                        }) => {
                            assert!(refinement.on_self(), "Cannot refine a marker on a type (tried assigning refinement {refinement} to {:?})", desc.0);
                            desc.2.push(marker)
                        }
                        Annotation::OType(id) => desc.1.push(id),
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
