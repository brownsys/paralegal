//! Compute program dependence graphs (PDG) for a function call graph.
#![feature(rustc_private, box_patterns)]

extern crate either;
extern crate rustc_abi;
extern crate rustc_borrowck;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_type_ir;

pub use utils::FnResolution;

use self::graph::DepGraph;
use construct::GraphConstructor;
pub use construct::{
    is_async_trait_fn, CallChanges, CallInfo, FakeEffect, FakeEffectKind, PdgParams, SkipCall,
};

mod construct;
pub mod graph;
mod utils;

/// Computes a global program dependence graph (PDG) starting from the root function specified by `def_id`.
pub fn compute_pdg(params: PdgParams<'_>) -> DepGraph<'_> {
    let constructor = GraphConstructor::root(params);
    constructor.construct()
}
