#![feature(
    rustc_private,
    box_patterns,
    associated_type_defaults,
    min_specialization,
    type_alias_impl_trait,
    trait_alias,
    negative_impls
)]
#![allow(
    clippy::single_match,
    clippy::needless_lifetimes,
    clippy::needless_return,
    clippy::len_zero,
    clippy::len_without_is_empty
)]
#![warn(missing_docs)]

extern crate either;
extern crate polonius_engine;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_graphviz;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_mir_transform;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;
extern crate smallvec;

pub mod mir;
