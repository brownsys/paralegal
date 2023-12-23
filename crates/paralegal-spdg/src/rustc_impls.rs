use super::rustc_proxies::*;
use super::*;
use crate::rustc::{def_id, hir, mir, span};

pub fn bbref_to_u32(r: &mir::BasicBlock) -> u32 {
    r.as_u32()
}

impl From<BasicBlock> for mir::BasicBlock {
    fn from(bb: BasicBlock) -> mir::BasicBlock {
        mir::BasicBlock::from_u32(bb.private)
    }
}

impl From<Location> for mir::Location {
    fn from(
        Location {
            block,
            statement_index,
        }: Location,
    ) -> mir::Location {
        mir::Location {
            block,
            statement_index,
        }
    }
}

impl From<mir::Location> for Location {
    fn from(
        mir::Location {
            block,
            statement_index,
        }: mir::Location,
    ) -> Location {
        Location {
            block,
            statement_index,
        }
    }
}

pub fn item_local_id_as_u32(i: &hir::ItemLocalId) -> u32 {
    i.as_u32()
}

impl From<ItemLocalId> for hir::ItemLocalId {
    fn from(proxy: ItemLocalId) -> hir::ItemLocalId {
        hir::ItemLocalId::from_u32(proxy.private)
    }
}

pub fn def_index_as_u32(i: &def_id::DefIndex) -> u32 {
    i.as_u32()
}

pub fn crate_num_as_u32(num: &hir::def_id::CrateNum) -> u32 {
    (*num).into()
}

impl From<rustc_proxies::DefId> for hir::def_id::DefId {
    fn from(value: rustc_proxies::DefId) -> Self {
        Self {
            krate: value.krate,
            index: value.index,
        }
    }
}

impl From<hir::def_id::DefId> for rustc_proxies::DefId {
    fn from(value: hir::def_id::DefId) -> Self {
        Self {
            krate: value.krate,
            index: value.index,
        }
    }
}

impl From<CrateNum> for hir::def_id::CrateNum {
    fn from(value: CrateNum) -> Self {
        hir::def_id::CrateNum::from_u32(value.private)
    }
}

impl From<DefIndex> for def_id::DefIndex {
    fn from(proxy: DefIndex) -> def_id::DefIndex {
        def_id::DefIndex::from_u32(proxy.private)
    }
}

impl Identifier {
    pub fn new(s: span::Symbol) -> Self {
        Identifier::new_intern(s.as_str())
    }
}
