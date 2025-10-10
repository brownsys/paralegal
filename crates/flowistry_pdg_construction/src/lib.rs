//! Compute program dependence graphs (PDG) for a function call graph.
#![feature(rustc_private, box_patterns, min_specialization)]

extern crate either;
extern crate polonius_engine;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_const_eval;
extern crate rustc_data_structures;
extern crate rustc_error_messages;
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

mod analysis;
pub mod callback;
pub mod constants;
pub mod source_access;
pub mod utils;

pub use analysis::async_support::{determine_async, is_async_trait_fn, match_async_trait_assign};
pub use analysis::global::call_tree_visit::{VisitDriver, Visitor};
pub use analysis::global::{
    DepEdge, DepEdgeKind, DepNode, DepNodeKind, MemoPdgConstructor, Node, OneHopLocation,
    PartialGraph, Use,
};
pub use analysis::CallingConvention;
pub use callback::{
    CallChangeCallback, CallChangeCallbackFn, CallChanges, CallInfo, InlineMissReason, SkipCall,
};
