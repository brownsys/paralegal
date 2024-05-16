use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefIndex, LocalDefId};
use rustc_middle::ty::TyCtxt;

use crate::{construct::SubgraphDescriptor, MemoPdgConstructor, PDGLoader};

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
                    (*constructor.construct_root(t).unwrap()).clone(),
                )
            })
            .collect::<FxHashMap<_, _>>()
    }

    pub fn new() -> Self {
        Self { targets: vec![] }
    }
}
