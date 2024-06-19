//! Data-and control flow analyzer and inliner.
//!
//! Analysis starts with the construction of [`SPDGGenerator`] from a
//! [`CollectingVisitor`](crate::discover::CollectingVisitor) and then calling
//! [`analyze`](SPDGGenerator::analyze).

use std::{rc::Rc, time::Duration};

use crate::{
    ann::{Annotation, MarkerAnnotation},
    desc::*,
    discover::FnToAnalyze,
    utils::*,
    DefId, HashMap, HashSet, LogLevelConfig, MarkerCtx, Symbol,
};

use anyhow::Result;

use flowistry_pdg_construction::MemoPdgConstructor;
use itertools::Itertools;
use petgraph::visit::GraphBase;

use rustc_hir::def;
use rustc_middle::ty::{Instance, ParamEnv, TyCtxt};
use rustc_span::{FileNameDisplayPreference, Span as RustSpan};

mod encoder;
mod graph_converter;
mod inline_judge;
mod metadata;

use graph_converter::GraphConverter;
use metadata::RustcInstructionKind;

pub use metadata::MetadataLoader;

/// Read-only database of information the analysis needs.
///
/// [`Self::analyze`] serves as the main entrypoint to SPDG generation.
pub struct SPDGGenerator<'tcx> {
    pub opts: &'static crate::Args,
    pub tcx: TyCtxt<'tcx>,
    marker_ctx: MarkerCtx<'tcx>,
    constructor: MemoPdgConstructor<'tcx>,
    metadata_loader: Rc<MetadataLoader<'tcx>>,
}

impl<'tcx> SPDGGenerator<'tcx> {
    pub fn new(
        marker_ctx: MarkerCtx<'tcx>,
        opts: &'static crate::Args,
        tcx: TyCtxt<'tcx>,
        constructor: MemoPdgConstructor<'tcx>,
        metadata_loader: Rc<MetadataLoader<'tcx>>,
    ) -> Self {
        Self {
            marker_ctx,
            opts,
            tcx,
            metadata_loader,
            constructor,
        }
    }

    pub fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        &self.marker_ctx
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
            .map(|controllers| self.make_program_description(controllers, known_def_ids, &targets))
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

        let instruction_info = self.collect_instruction_info(&controllers, &mut known_def_ids);

        let type_info = self.collect_type_info();
        known_def_ids.extend(type_info.keys());
        let def_info = known_def_ids
            .iter()
            .map(|id| (*id, def_info_for_item(*id, self.marker_ctx(), tcx)))
            .collect();

        type_info_sanity_check(&controllers, &type_info);
        ProgramDescription {
            type_info,
            instruction_info,
            controllers,
            def_info,
            rustc_time: Duration::ZERO,
            marker_annotation_count: 0,
            dedup_locs: 0,
            dedup_functions: 0,
            seen_locs: 0,
            seen_functions: 0,
            analyzed_spans: Default::default(),
        }
    }

    /// Create an [`InstructionInfo`] record for each [`GlobalLocation`]
    /// mentioned in the controllers.
    fn collect_instruction_info(
        &self,
        controllers: &HashMap<Endpoint, SPDG>,
        known_def_ids: &mut impl Extend<DefId>,
    ) -> HashMap<CallString, InstructionInfo> {
        let all_instructions = controllers
            .values()
            .flat_map(|v| {
                v.graph
                    .node_weights()
                    .map(|n| &n.at)
                    .chain(v.graph.edge_weights().map(|e| &e.at))
            })
            .collect::<HashSet<_>>();
        all_instructions
            .into_iter()
            .map(|&n| {
                let monos = self.metadata_loader.get_mono(n).unwrap();
                let body = self
                    .metadata_loader
                    .get_body_info(n.leaf().function)
                    .unwrap();
                let (kind, description, span) = match n.leaf().location {
                    RichLocation::End => {
                        (InstructionKind::Return, "start".to_owned(), body.def_span)
                    }
                    RichLocation::Start => {
                        (InstructionKind::Start, "end".to_owned(), body.def_span)
                    }
                    RichLocation::Location(loc) => {
                        let instruction = body.instruction_at(loc);
                        (
                            match instruction.kind {
                                RustcInstructionKind::SwitchInt => InstructionKind::SwitchInt,
                                RustcInstructionKind::FunctionCall(c) => {
                                    InstructionKind::FunctionCall({
                                        let (id, generics) =
                                            flowistry_pdg_construction::utils::type_as_fn(
                                                self.tcx,
                                                c.instantiate(self.tcx, monos),
                                            )
                                            .unwrap();
                                        let instance_id = Instance::resolve(
                                            self.tcx,
                                            ParamEnv::reveal_all(),
                                            id,
                                            generics,
                                        )
                                        .unwrap()
                                        .map(|i| i.def_id())
                                        .unwrap_or(id);
                                        known_def_ids.extend(Some(instance_id));
                                        FunctionCallInfo { id: instance_id }
                                    })
                                }
                                RustcInstructionKind::Statement => InstructionKind::Statement,
                                RustcInstructionKind::Terminator => InstructionKind::Terminator,
                            },
                            (*instruction.description).clone(),
                            instruction.span,
                        )
                    }
                };
                (
                    n,
                    InstructionInfo {
                        kind,
                        span: src_loc_for_span(span, self.tcx),
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
                    match ann.as_ref() {
                        Annotation::Marker(MarkerAnnotation { refinement, marker }) => {
                            assert!(refinement.on_self());
                            desc.2.push(*marker)
                        }
                        Annotation::OType(id) => desc.1.push(*id),
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
                        markers: markers
                            .into_iter()
                            .map(|i| Identifier::new_intern(i.as_str()))
                            .collect(),
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
            use rustc_hir::definitions::DefPathDataName::*;
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
                marker: Identifier::new_intern(ann.marker.as_str()),
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
