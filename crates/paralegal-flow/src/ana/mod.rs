//! Data-and control flow analyzer and inliner.
//!
//! Analysis starts with the construction of [`SPDGGenerator`] from a
//! [`CollectingVisitor`](crate::discover::CollectingVisitor) and then calling
//! [`analyze`](SPDGGenerator::analyze).

use crate::{
    ann::{db::MarkerDatabase, Annotation, MarkerAnnotation},
    consts::INTERMEDIATE_ARTIFACT_EXT,
    desc::*,
    discover::{CollectingVisitor, FnToAnalyze},
    utils::*,
    Args, DefId, HashMap, HashSet, LogLevelConfig, MarkerCtx, Symbol,
};

use std::path::Path;
use std::{fs::File, io::Read, rc::Rc};

use flowistry_pdg_construction::{
    graph::InternedString, Asyncness, DepGraph, MemoPdgConstructor, PDGLoader, SubgraphDescriptor,
};
use itertools::Itertools;
use petgraph::visit::GraphBase;

use rustc_hash::FxHashMap;
use rustc_hir::{
    def,
    def_id::{CrateNum, DefIndex, LOCAL_CRATE},
};
use rustc_index::IndexVec;
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::{
    mir::{
        BasicBlock, HasLocalDecls, Local, LocalDecl, LocalDecls, LocalKind, Location,
        TerminatorKind,
    },
    ty::{tls, GenericArgsRef, TyCtxt},
};
use rustc_serialize::{Decodable, Encodable};
use rustc_span::{FileNameDisplayPreference, Span as RustSpan};

mod encoder;
mod graph_converter;
mod inline_judge;

use anyhow::Result;
use graph_converter::GraphConverter;
use rustc_utils::{cache::Cache, mir::borrowck_facts};
use thiserror::Error;

use self::{
    encoder::{ParalegalDecoder, ParalegalEncoder},
    graph_converter::MyCallback,
    inline_judge::InlineJudge,
};

pub struct MetadataLoader<'tcx> {
    tcx: TyCtxt<'tcx>,
    cache: Cache<CrateNum, Option<Metadata<'tcx>>>,
}

#[derive(Debug, Error)]
pub enum MetadataLoaderError {
    #[error("no pdg for item {:?}", .0)]
    NoPdgForItem(DefId),
    #[error("no metadata for crate {}", tls::with(|tcx| tcx.crate_name(*.0)))]
    NoMetadataForCrate(CrateNum),
    #[error("no generics known for call site {0}")]
    NoGenericsKnownForCallSite(CallString),
    #[error("no metadata for item {:?} in crate {}", .0, tls::with(|tcx| tcx.crate_name(.0.krate)))]
    NoSuchItemInCate(DefId),
}

use MetadataLoaderError::*;

impl<'tcx> PDGLoader<'tcx> for MetadataLoader<'tcx> {
    fn load(&self, function: DefId) -> Option<&SubgraphDescriptor<'tcx>> {
        self.get_metadata(function.krate)
            .ok()?
            .pdgs
            .get(&function.index)
    }
}

impl<'tcx> MetadataLoader<'tcx> {
    pub fn collect_and_emit_metadata(
        self: Rc<Self>,
        args: &'static Args,
        path: impl AsRef<Path>,
    ) -> (Vec<FnToAnalyze>, MarkerCtx<'tcx>, MemoPdgConstructor<'tcx>) {
        let tcx = self.tcx;
        let mut collector = CollectingVisitor::new(tcx, args, self.clone());
        collector.run();
        let emit_targets = collector.emit_target_collector;
        let marker_ctx: MarkerCtx = collector.marker_ctx.into();
        let mut constructor = MemoPdgConstructor::new(tcx, self.clone());
        constructor.with_call_change_callback(MyCallback {
            tcx,
            judge: InlineJudge::new(marker_ctx.clone(), tcx, args.anactrl()),
        });
        let pdgs = emit_targets
            .into_iter()
            .map(|t| {
                (
                    t.local_def_index,
                    (*constructor.construct_root(t).unwrap()).clone(),
                )
            })
            .collect::<FxHashMap<_, _>>();
        let meta = Metadata::from_pdgs(tcx, pdgs, marker_ctx.db());
        let path = path.as_ref();
        println!("Writing metadata to {}", path.display());
        meta.write(path, tcx);
        self.cache.get(LOCAL_CRATE, |_| Some(meta));
        (collector.functions_to_analyze, marker_ctx, constructor)
    }

    pub fn get_annotations(&self, key: DefId) -> &[Annotation] {
        (|| {
            Some(
                self.get_metadata(key.krate)
                    .ok()?
                    .local_annotations
                    .get(&key.index)?
                    .as_slice(),
            )
        })()
        .unwrap_or(&[])
    }

    pub fn all_annotations<'a>(&'a self) -> impl Iterator<Item = (DefId, &'a Annotation)> {
        let b = self.cache.borrow();

        // Safety: While we're keeping references to the borrow above, we only
        // keep references to values behind `Pin<Box<_>>` which are guaranteed
        // not to move. So even if the borrow is modified, these references are
        // still valid.
        //
        // In terms of race conditions: this is a cache which never overwrites values.
        let metadatas = unsafe {
            std::mem::transmute::<
                Vec<(CrateNum, &_)>,
                Vec<(CrateNum, &'a HashMap<DefIndex, Vec<Annotation>>)>,
            >(
                b.iter()
                    .filter_map(|(k, v)| Some((*k, &(**(v.as_ref()?)).as_ref()?.local_annotations)))
                    .collect::<Vec<_>>(),
            )
        };
        metadatas.into_iter().flat_map(|(krate, m)| {
            m.iter()
                .flat_map(move |(&index, v)| v.iter().map(move |v| (DefId { krate, index }, v)))
        })
    }
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct Metadata<'tcx> {
    pub pdgs: FxHashMap<DefIndex, SubgraphDescriptor<'tcx>>,
    pub bodies: FxHashMap<DefIndex, BodyInfo<'tcx>>,
    pub local_annotations: HashMap<DefIndex, Vec<Annotation>>,
    pub reachable_markers: HashMap<(DefIndex, Option<GenericArgsRef<'tcx>>), Box<[InternedString]>>,
}

impl<'tcx> Metadata<'tcx> {
    fn write(&self, path: impl AsRef<Path>, tcx: TyCtxt<'tcx>) {
        let mut encoder = ParalegalEncoder::new(path, tcx);
        self.encode(&mut encoder);
        encoder.finish()
    }
}

impl<'tcx> Metadata<'tcx> {
    pub fn from_pdgs(
        tcx: TyCtxt<'tcx>,
        pdgs: FxHashMap<DefIndex, SubgraphDescriptor<'tcx>>,
        markers: &MarkerDatabase<'tcx>,
    ) -> Self {
        let mut bodies: FxHashMap<DefIndex, BodyInfo> = Default::default();
        for pdg in pdgs.values().flat_map(|d| {
            d.graph
                .nodes
                .iter()
                .map(|n| &n.at)
                .chain(d.graph.edges.iter().map(|e| &e.2.at))
                .flat_map(|at| at.iter())
        }) {
            if let Some(local) = pdg.function.as_local() {
                let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, local);
                let body = &body_with_facts.body;
                bodies
                    .entry(local.local_def_index)
                    .or_insert_with(|| BodyInfo {
                        arg_count: body.arg_count,
                        decls: body.local_decls().to_owned(),
                        instructions: body
                            .basic_blocks
                            .iter()
                            .map(|bb| {
                                let t = bb.terminator();
                                bb.statements
                                    .iter()
                                    .map(|s| RustcInstructionInfo {
                                        kind: RustcInstructionKind::Statement,
                                        span: s.source_info.span,
                                        description: format!("{:?}", s.kind).into(),
                                    })
                                    .chain([RustcInstructionInfo {
                                        kind: if let Ok((id, ..)) = t.as_fn_and_args(tcx) {
                                            RustcInstructionKind::FunctionCall(FunctionCallInfo {
                                                id,
                                            })
                                        } else if matches!(t.kind, TerminatorKind::SwitchInt { .. })
                                        {
                                            RustcInstructionKind::SwitchInt
                                        } else {
                                            RustcInstructionKind::Terminator
                                        },
                                        span: t.source_info.span,
                                        description: format!("{:?}", t.kind).into(),
                                    }])
                                    .collect()
                            })
                            .collect(),
                        def_span: tcx.def_span(local),
                    });
            }
        }
        let cache_borrow = markers.reachable_markers.borrow();
        Self {
            pdgs,
            bodies,
            local_annotations: markers
                .local_annotations
                .iter()
                .map(|(k, v)| (k.local_def_index, v.clone()))
                .collect(),
            reachable_markers: (&*cache_borrow)
                .iter()
                .filter_map(|(k, v)| {
                    let (id, args) = match k {
                        FnResolution::Partial(d) => (*d, None),
                        FnResolution::Final(inst) => (inst.def_id(), Some(inst.args)),
                    };
                    Some((
                        (id.as_local()?.local_def_index, args),
                        (**(v.as_ref()?)).clone(),
                    ))
                })
                .collect(),
        }
    }
}

impl<'tcx> MetadataLoader<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Rc<Self> {
        Rc::new(Self {
            tcx,
            cache: Default::default(),
        })
    }

    pub fn get_metadata(&self, key: CrateNum) -> Result<&Metadata<'tcx>> {
        let meta = self
            .cache
            .get(key, |_| {
                let paths = self.tcx.crate_extern_paths(key);
                for path in paths {
                    let path = path.with_extension(INTERMEDIATE_ARTIFACT_EXT);
                    println!("Trying to load file {}", path.display());
                    let Ok(mut file) = File::open(path) else {
                        continue;
                    };
                    let mut buf = Vec::new();
                    file.read_to_end(&mut buf).unwrap();
                    let mut decoder = ParalegalDecoder::new(self.tcx, buf.as_slice());
                    let meta = Metadata::decode(&mut decoder);
                    println!("Successfully loaded");
                    return Some(meta);
                }
                None
            })
            .as_ref()
            .ok_or(NoMetadataForCrate(key))?;
        Ok(meta)
    }

    pub fn get_body_info(&self, key: DefId) -> Result<&BodyInfo<'tcx>> {
        let meta = self.get_metadata(key.krate)?;
        let res = meta.bodies.get(&key.index).ok_or(NoSuchItemInCate(key));
        if res.is_err() {
            println!("Known items are");
            for &index in meta.bodies.keys() {
                println!(
                    "  {:?}",
                    DefId {
                        krate: key.krate,
                        index
                    }
                );
            }
        }
        Ok(res?)
    }

    pub fn get_mono(&self, cs: CallString) -> Result<GenericArgsRef<'tcx>> {
        let get_graph = |key: DefId| {
            let meta = self.get_metadata(key.krate)?;
            println!("Pdgs are known for");
            for &index in meta.pdgs.keys() {
                println!(
                    "  {:?}",
                    DefId {
                        krate: key.krate,
                        index
                    }
                );
            }
            anyhow::Ok(&meta.pdgs.get(&key.index).ok_or(NoPdgForItem(key))?.graph)
        };
        if let Some(caller) = cs.caller() {
            let key = caller.root().function;
            let monos = &get_graph(key)?.monos;
            // println!("Known monos for {key:?} are");
            // for (k, v) in monos {
            //     println!("  {k}: {v:?}");
            // }
            Ok(*monos.get(&caller).ok_or(NoGenericsKnownForCallSite(cs))?)
        } else {
            Ok(get_graph(cs.leaf().function)?.generics)
        }
    }

    pub fn get_pdg(&self, key: DefId) -> Result<DepGraph<'tcx>> {
        Ok(self
            .get_metadata(key.krate)?
            .pdgs
            .get(&key.index)
            .ok_or(NoPdgForItem(key))?
            .to_petgraph())
    }

    pub fn get_asyncness(&self, key: DefId) -> Asyncness {
        (|| {
            Some(
                self.get_metadata(key.krate)
                    .ok()?
                    .pdgs
                    .get(&key.index)?
                    .graph
                    .asyncness,
            )
        })()
        .unwrap_or(Asyncness::No)
    }
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct BodyInfo<'tcx> {
    pub arg_count: usize,
    pub decls: IndexVec<Local, LocalDecl<'tcx>>,
    pub instructions: IndexVec<BasicBlock, Vec<RustcInstructionInfo>>,
    pub def_span: rustc_span::Span,
}

#[derive(Clone, Copy, Debug, Encodable, Decodable)]
pub struct RustcInstructionInfo {
    /// Classification of the instruction
    pub kind: RustcInstructionKind,
    /// The source code span
    pub span: rustc_span::Span,
    /// Textual rendering of the MIR
    pub description: InternedString,
}

/// The type of instructions we may encounter
#[derive(Debug, Clone, Copy, Eq, Ord, PartialOrd, PartialEq, Encodable, Decodable)]
pub enum RustcInstructionKind {
    /// Some type of statement
    Statement,
    /// A function call
    FunctionCall(FunctionCallInfo),
    /// A basic block terminator
    Terminator,
    /// The switch int terminator
    SwitchInt,
}

impl<'tcx> BodyInfo<'tcx> {
    pub fn local_kind(&self, local: Local) -> LocalKind {
        let local = local.as_usize();
        assert!(local < self.decls.len());
        if local == 0 {
            LocalKind::ReturnPointer
        } else if local < self.arg_count + 1 {
            LocalKind::Arg
        } else {
            LocalKind::Temp
        }
    }

    pub fn instruction_at(&self, location: Location) -> RustcInstructionInfo {
        self.instructions[location.block][location.statement_index]
    }

    pub fn span_of(&self, loc: RichLocation) -> rustc_span::Span {
        match loc {
            RichLocation::Location(loc) => self.instruction_at(loc).span,
            _ => self.def_span,
        }
    }
}

impl<'tcx> HasLocalDecls<'tcx> for BodyInfo<'tcx> {
    fn local_decls(&self) -> &LocalDecls<'tcx> {
        &self.decls
    }
}

/// Read-only database of information the analysis needs.
///
/// [`Self::analyze`] serves as the main entrypoint to SPDG generation.
pub struct SPDGGenerator<'tcx> {
    pub opts: &'static crate::Args,
    pub tcx: TyCtxt<'tcx>,
    marker_ctx: MarkerCtx<'tcx>,
    flowistry_loader: MemoPdgConstructor<'tcx>,
    metadata_loader: Rc<MetadataLoader<'tcx>>,
}

impl<'tcx> SPDGGenerator<'tcx> {
    pub fn new(
        marker_ctx: MarkerCtx<'tcx>,
        opts: &'static crate::Args,
        tcx: TyCtxt<'tcx>,
        loader: MemoPdgConstructor<'tcx>,
        metadata_loader: Rc<MetadataLoader<'tcx>>,
    ) -> Self {
        Self {
            marker_ctx,
            opts,
            tcx,
            flowistry_loader: loader,
            metadata_loader,
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
                let desc = self.make_program_description(controllers, known_def_ids, &targets);

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
            .filter_map(|l| l.function.as_local())
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
                .filter(|m| m.1.as_marker().is_some())
                .count() as u32,
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
                    .map(|n| &n.at)
                    .chain(v.graph.edge_weights().map(|e| &e.at))
            })
            .flat_map(|at| at.iter())
            .collect::<HashSet<_>>();
        all_instructions
            .into_iter()
            .map(|n| {
                let body = self.metadata_loader.get_body_info(n.function).unwrap();
                let (kind, description, span) = match n.location {
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
                                    InstructionKind::FunctionCall(c)
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
