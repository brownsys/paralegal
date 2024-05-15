use flowistry_pdg::{CallString, RichLocation};
use rustc_hash::FxHashMap;
use rustc_hir::{
    def_id::{CrateNum, DefId, DefIndex, LocalDefId},
    intravisit::{self, FnKind},
    BodyId,
};
use rustc_index::IndexVec;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::{
    hir::nested_filter::OnlyBodies,
    mir::{
        BasicBlock, HasLocalDecls, Local, LocalDecl, LocalDecls, LocalKind, Location,
        TerminatorKind,
    },
    ty::{GenericArgsRef, TyCtxt},
};
use rustc_span::Span;
use rustc_utils::{cache::Cache, mir::borrowck_facts};

use crate::{
    construct::SubgraphDescriptor, Asyncness, CallChangeCallback, DepGraph, MemoPdgConstructor,
    PDGLoader,
};

pub struct MetadataCollector {
    targets: Vec<LocalDefId>,
}

impl MetadataCollector {
    pub fn add_target(&mut self, target: LocalDefId) {
        self.targets.push(target)
    }

    pub fn into_metadata<'tcx>(
        self,
        tcx: TyCtxt<'tcx>,
        loader: impl PDGLoader<'tcx> + 'tcx,
    ) -> FxHashMap<DefIndex, SubgraphDescriptor<'tcx>> {
        let constructor = MemoPdgConstructor::new(tcx, loader);
        self.targets
            .into_iter()
            .map(|t| {
                (
                    t.local_def_index,
                    (*constructor
                        .construct_for(crate::FnResolution::Partial(t.to_def_id()))
                        .unwrap())
                    .clone(),
                )
            })
            .collect::<FxHashMap<_, _>>()
    }

    pub fn new() -> Self {
        Self { targets: vec![] }
    }
}
