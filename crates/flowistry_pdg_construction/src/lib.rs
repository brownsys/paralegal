//! Compute program dependence graphs (PDG) for a function call graph.
#![feature(rustc_private, box_patterns)]

extern crate either;
extern crate rustc_abi;
extern crate rustc_borrowck;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_serialize;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_type_ir;

pub use utils::FnResolution;

use self::graph::DepGraph;
pub use async_support::{determine_async, is_async_trait_fn, match_async_trait_assign};
pub mod callback;
pub use crate::construct::MemoPdgConstructor;
pub use callback::{
    CallChangeCallback, CallChangeCallbackFn, CallChanges, CallInfo, InlineMissReason, SkipCall,
};
use rustc_middle::ty::TyCtxt;
pub use utils::{is_non_default_trait_method, try_resolve_function};

mod async_support;
mod calling_convention;
mod construct;
pub mod graph;
mod mutation;
mod utils;

/// Computes a global program dependence graph (PDG) starting from the root function specified by `def_id`.
pub fn compute_pdg<'tcx>(tcx: TyCtxt<'tcx>, params: FnResolution<'tcx>) -> DepGraph<'tcx> {
    let constructor = MemoPdgConstructor::new(tcx);
    constructor.construct_for(params).unwrap().to_petgraph()
}
