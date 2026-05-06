//! MIR alias and place analysis for Paralegal's information flow engine.
//!
//! This crate answers two related questions about a function body:
//!
//! 1. **Alias analysis** ([`mir::aliases::Aliases`]) — given a reference place
//!    `*p`, which concrete places can it point to?  The analysis is
//!    region-based: it gathers all borrow expressions in the MIR, propagates
//!    the subset relation from borrowck facts (via [`mir::FlowistryInput`]), and
//!    computes a fixpoint that respects field projections.
//!
//! 2. **Place information** ([`mir::placeinfo::PlaceInfo`]) — a higher-level,
//!    cached view built on top of alias analysis that answers: what are the
//!    children / conflicts / reachable values of a place?
//!
//! # Typical usage
//!
//! ```ignore
//! let aliases = Aliases::build(tcx, def_id, body_with_facts);
//! let place_info = PlaceInfo::build(tcx, def_id, body_with_facts);
//! let pointed_to = aliases.aliases(some_deref_place);
//! let reachable  = place_info.reachable_values(some_place, Mutability::Mut);
//! ```
//!
//! Both constructors accept any type that implements [`mir::FlowistryInput`],
//! which is blanket-implemented for `&BodyWithBorrowckFacts`.
#![feature(rustc_private, min_specialization)]
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
