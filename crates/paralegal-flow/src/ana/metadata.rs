//! Per-crate intermediate data we store.
//!
//! [`Metadata`] is what gets stored, whereas a [`MetadataLoader`] is
//! responsible for reading/writing this data.

use crate::{
    ann::{db::MarkerDatabase, Annotation},
    consts::INTERMEDIATE_ARTIFACT_EXT,
    desc::*,
    discover::{CollectingVisitor, FnToAnalyze},
    Args, DefId, HashMap, MarkerCtx,
};

use std::path::Path;
use std::{fs::File, io::Read, rc::Rc};

use flowistry_pdg_construction::{
    graph::InternedString, GraphLoader, Asyncness, DepGraph, MemoPdgConstructor, PartialGraph,
};

use rustc_hash::FxHashMap;
use rustc_hir::def_id::{CrateNum, DefIndex, LocalDefId, LOCAL_CRATE};
use rustc_index::IndexVec;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::{
    mir::{
        BasicBlock, BasicBlockData, HasLocalDecls, Local, LocalDecl, LocalDecls, LocalKind,
        Location, Statement, Terminator, TerminatorKind,
    },
    ty::{tls, EarlyBinder, GenericArgsRef, Ty, TyCtxt},
};
use rustc_serialize::{Decodable, Encodable};

use anyhow::Result;
use rustc_utils::{cache::Cache, mir::borrowck_facts};
use thiserror::Error;

use super::{
    encoder::{ParalegalDecoder, ParalegalEncoder},
    graph_converter::MyCallback,
    inline_judge::InlineJudge,
};

/// Manager responsible for reading and writing [`Metadata`] artifacts.
pub struct MetadataLoader<'tcx> {
    tcx: TyCtxt<'tcx>,
    cache: Cache<CrateNum, Option<Metadata<'tcx>>>,
}

/// The types of errors that can arise from interacting with the [`MetadataLoader`].
#[derive(Debug, Error)]
pub enum MetadataLoaderError {
    #[error("no pdg for item {:?}", .0)]
    PdgForItemMissing(DefId),
    #[error("no metadata for crate {}", tls::with(|tcx| tcx.crate_name(*.0)))]
    MetadataForCrateMissing(CrateNum),
    #[error("no generics known for call site {0}")]
    NoGenericsKnownForCallSite(CallString),
    #[error("no metadata for item {:?} in crate {}", .0, tls::with(|tcx| tcx.crate_name(.0.krate)))]
    NoSuchItemInCate(DefId),
}

use MetadataLoaderError::*;

impl<'tcx> GraphLoader<'tcx> for MetadataLoader<'tcx> {
    fn load(&self, function: DefId) -> Option<&PartialGraph<'tcx>> {
        let res = self
            .get_metadata(function.krate)
            .ok()?
            .pdgs
            .get(&function.index);
        res
    }
}

impl<'tcx> MetadataLoader<'tcx> {
    /// Traverse the items of this crate, create PDGs and collect other relevant
    /// information about them. Write the metadata to disk, but also register
    /// them with the loader itself for downstream analyses.
    ///
    /// Returns which functions should be emitted for policy enforcement (e.g.
    /// analysis targets) and a context of discovered markers suitable for query
    /// during that analysis.
    pub fn collect_and_emit_metadata(
        self: Rc<Self>,
        args: &'static Args,
        path: impl AsRef<Path>,
    ) -> (Vec<FnToAnalyze>, MarkerCtx<'tcx>) {
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
        debug!("Writing metadata to {}", path.display());
        meta.write(path, tcx);
        self.cache.get(LOCAL_CRATE, |_| Some(meta));
        (collector.functions_to_analyze, marker_ctx)
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

/// Intermediate artifacts stored on disc for every crate.
///
/// Contains PDGs and reduced information about the source code that is needed
/// downstream.
#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct Metadata<'tcx> {
    pub pdgs: FxHashMap<DefIndex, PartialGraph<'tcx>>,
    pub bodies: FxHashMap<DefIndex, BodyInfo<'tcx>>,
    pub local_annotations: HashMap<DefIndex, Vec<Annotation>>,
    pub reachable_markers: HashMap<(DefIndex, GenericArgsRef<'tcx>), Box<[InternedString]>>,
}

impl<'tcx> Metadata<'tcx> {
    fn write(&self, path: impl AsRef<Path>, tcx: TyCtxt<'tcx>) {
        let mut encoder = ParalegalEncoder::new(path, tcx);
        self.encode(&mut encoder);
        encoder.finish()
    }
}

impl<'tcx> Metadata<'tcx> {
    /// Given a set of PDGs created, query additional information we need to
    /// record from rustc and return a serializable metadata artifact.
    pub fn from_pdgs(
        tcx: TyCtxt<'tcx>,
        pdgs: FxHashMap<DefIndex, PartialGraph<'tcx>>,
        markers: &MarkerDatabase<'tcx>,
    ) -> Self {
        let mut bodies: FxHashMap<DefIndex, BodyInfo> = Default::default();
        for call_string in pdgs
            .values()
            .flat_map(|subgraph| subgraph.mentioned_call_string())
        {
            for location in call_string.iter() {
                if let Some(local) = location.function.as_local() {
                    bodies.entry(local.local_def_index).or_insert_with(|| {
                        let info = BodyInfo::from_body(tcx, local);
                        trace!("Created info for body {local:?}\n{info:?}");
                        info
                    });
                }
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
            reachable_markers: (*cache_borrow)
                .iter()
                .filter_map(|(inst, v)| {
                    let id = inst.def_id();
                    let args = inst.args;
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
                    let Ok(mut file) = File::open(path) else {
                        continue;
                    };
                    let mut buf = Vec::new();
                    file.read_to_end(&mut buf).unwrap();
                    let mut decoder = ParalegalDecoder::new(self.tcx, buf.as_slice());
                    let meta = Metadata::decode(&mut decoder);
                    return Some(meta);
                }
                None
            })
            .as_ref()
            .ok_or(MetadataForCrateMissing(key))?;
        Ok(meta)
    }

    pub fn get_body_info(&self, key: DefId) -> Result<&BodyInfo<'tcx>> {
        let meta = self.get_metadata(key.krate)?;
        let res = meta.bodies.get(&key.index).ok_or(NoSuchItemInCate(key));
        Ok(res?)
    }

    pub fn get_mono(&self, cs: CallString) -> Result<GenericArgsRef<'tcx>> {
        let key = cs.root().function;
        let meta = self.get_metadata(key.krate)?;
        Ok(meta
            .pdgs
            .get(&key.index)
            .ok_or(PdgForItemMissing(key))?
            .get_mono(cs)
            .ok_or(NoGenericsKnownForCallSite(cs))?)
    }

    pub fn get_pdg(&self, key: DefId) -> Result<DepGraph<'tcx>> {
        Ok(self
            .get_metadata(key.krate)?
            .pdgs
            .get(&key.index)
            .ok_or(PdgForItemMissing(key))?
            .to_petgraph())
    }

    pub fn get_asyncness(&self, key: DefId) -> Asyncness {
        (|| {
            Some(
                self.get_metadata(key.krate)
                    .ok()?
                    .pdgs
                    .get(&key.index)?
                    .asyncness(),
            )
        })()
        .unwrap_or(Asyncness::No)
    }
}

/// Effectively a reduced MIR [`Body`](rustc_middle::mir::Body).
#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct BodyInfo<'tcx> {
    pub arg_count: usize,
    pub decls: IndexVec<Local, LocalDecl<'tcx>>,
    pub instructions: IndexVec<BasicBlock, Vec<RustcInstructionInfo<'tcx>>>,
    pub def_span: rustc_span::Span,
}

impl<'tcx> BodyInfo<'tcx> {
    pub fn from_body(tcx: TyCtxt<'tcx>, function_id: LocalDefId) -> Self {
        let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, function_id);
        let body = &body_with_facts.body;
        Self {
            arg_count: body.arg_count,
            decls: body.local_decls().to_owned(),
            instructions: body
                .basic_blocks
                .iter()
                .map(|bb| RustcInstructionInfo::from_basic_block(tcx, body, bb))
                .collect(),
            def_span: tcx.def_span(function_id),
        }
    }
}

#[derive(Clone, Copy, Debug, TyEncodable, TyDecodable)]
pub struct RustcInstructionInfo<'tcx> {
    /// Classification of the instruction
    pub kind: RustcInstructionKind<'tcx>,
    /// The source code span
    pub span: rustc_span::Span,
    /// Textual rendering of the MIR
    pub description: InternedString,
}

impl<'tcx> RustcInstructionInfo<'tcx> {
    pub fn from_statement(stmt: &Statement) -> Self {
        Self {
            kind: RustcInstructionKind::Statement,
            span: stmt.source_info.span,
            description: format!("{:?}", stmt.kind).into(),
        }
    }

    pub fn from_terminator(
        tcx: TyCtxt<'tcx>,
        local_decls: &impl HasLocalDecls<'tcx>,
        term: &Terminator<'tcx>,
    ) -> Self {
        Self {
            kind: match &term.kind {
                TerminatorKind::Call {
                    func,
                    args: _,
                    destination: _,
                    target: _,
                    unwind: _,
                    call_source: _,
                    fn_span: _,
                } => {
                    let op_ty = tcx.erase_regions(func.ty(local_decls, tcx));
                    RustcInstructionKind::FunctionCall(EarlyBinder::bind(op_ty))
                }
                TerminatorKind::SwitchInt { .. } => RustcInstructionKind::SwitchInt,
                _ => RustcInstructionKind::Terminator,
            },
            span: term.source_info.span,
            description: format!("{:?}", term.kind).into(),
        }
    }

    pub fn from_basic_block(
        tcx: TyCtxt<'tcx>,
        local_decls: &impl HasLocalDecls<'tcx>,
        bb: &BasicBlockData<'tcx>,
    ) -> Vec<Self> {
        let t = bb.terminator();
        bb.statements
            .iter()
            .map(Self::from_statement)
            .chain([Self::from_terminator(tcx, local_decls, t)])
            .collect()
    }
}

/// The type of instructions we may encounter
#[derive(Debug, Clone, Copy, Eq, Ord, PartialOrd, PartialEq, TyEncodable, TyDecodable)]
pub enum RustcInstructionKind<'tcx> {
    /// Some type of statement
    Statement,
    /// A function call. The type is guaranteed to be of function type
    FunctionCall(EarlyBinder<Ty<'tcx>>),
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

    pub fn instruction_at(&self, location: Location) -> RustcInstructionInfo<'tcx> {
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
