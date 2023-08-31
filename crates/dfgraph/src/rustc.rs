use super::*;
use rustc_hir::{self as hir, def_id};
use rustc_middle::mir;

pub fn bbref_to_usize(r: &mir::BasicBlock) -> usize {
    r.as_usize()
}

impl From<BasicBlock> for mir::BasicBlock {
    fn from(bb: BasicBlock) -> mir::BasicBlock {
        mir::BasicBlock::from_usize(bb.private)
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

impl From<DefIndex> for def_id::DefIndex {
    fn from(proxy: DefIndex) -> def_id::DefIndex {
        def_id::DefIndex::from_u32(proxy.private)
    }
}

impl Identifier {
    pub fn new(s: rustc_span::Symbol) -> Self {
        Identifier::new_intern(s.as_str())
    }
}
