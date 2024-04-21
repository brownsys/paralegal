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
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_type_ir;

pub use utils::FnResolution;

use self::graph::DepGraph;
pub use async_support::{determine_async, is_async_trait_fn, match_async_trait_assign};
use construct::GraphConstructor;
pub mod callback;
pub use callback::{
    CallChangeCallback, CallChangeCallbackFn, CallChanges, CallInfo, FakeEffect, FakeEffectKind,
    InlineMissReason, SkipCall,
};
pub use construct::PdgParams;
pub use utils::{is_non_default_trait_method, try_resolve_function};

mod async_support;
mod calling_convention;
mod construct;
pub mod graph;
mod mutation;
mod utils;

/// Computes a global program dependence graph (PDG) starting from the root function specified by `def_id`.
pub fn compute_pdg(params: PdgParams<'_>) -> DepGraph<'_> {
    let constructor = GraphConstructor::root(params);
    constructor.construct()
}
