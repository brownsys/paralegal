//! Compute program dependence graphs (PDG) for a function call graph.
#![feature(rustc_private, box_patterns, min_specialization)]

extern crate either;
extern crate polonius_engine;
extern crate rustc_abi;
extern crate rustc_borrowck;
extern crate rustc_const_eval;
extern crate rustc_data_structures;
extern crate rustc_errors;
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

use self::graph::DepGraph;
pub use async_support::{determine_async, is_async_trait_fn, match_async_trait_assign};
use rustc_hir::def_id::LocalDefId;
pub mod callback;
pub use crate::construct::MemoPdgConstructor;
pub use callback::{
    CallChangeCallback, CallChangeCallbackFn, CallChanges, CallInfo, InlineMissReason, SkipCall,
};
use rustc_middle::ty::TyCtxt;

mod approximation;
mod async_support;
pub mod body_cache;
pub mod calling_convention;
mod construct;
pub mod encoder;
pub mod graph;
mod local_analysis;
mod mutation;
pub mod utils;

/// Computes a global program dependence graph (PDG) starting from the root function specified by `def_id`.
pub fn compute_pdg(tcx: TyCtxt<'_>, def_id: LocalDefId) -> DepGraph<'_> {
    let constructor = MemoPdgConstructor::new(tcx);
    constructor.construct_graph(def_id)
}
