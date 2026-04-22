#![feature(rustc_private, min_specialization)]
#![warn(clippy::pedantic)]
#![allow(
    clippy::len_zero,
    clippy::len_without_is_empty,
    clippy::must_use_candidate,
    clippy::return_self_not_must_use,
    clippy::missing_panics_doc,
    clippy::missing_errors_doc,
    clippy::doc_markdown,
    clippy::single_match_else,
    clippy::if_not_else,
    clippy::match_on_vec_items,
    clippy::map_unwrap_or,
    clippy::match_wildcard_for_single_variants,
    clippy::items_after_statements,
    clippy::implicit_hasher,
    clippy::wildcard_imports
)]

extern crate either;
extern crate rustc_abi;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_graphviz;
extern crate rustc_hir;
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

pub mod cache;
pub mod hir;
pub mod mir;
pub mod source_map;
#[cfg(feature = "test")]
pub mod test_utils;

pub use crate::{
    hir::ty::TyExt,
    mir::{
        adt_def::AdtDefExt, body::BodyExt, mutability::MutabilityExt, operand::OperandExt,
        place::PlaceExt,
    },
};

#[macro_export]
macro_rules! hashset {
  (@single $($x:tt)*) => (());
  (@count $($rest:expr),*) => (<[()]>::len(&[$(hashset!(@single $rest)),*]));

  ($($key:expr,)+) => { hashset!($($key),+) };
  ($($key:expr),*) => {
      {
          let _cap = hashset!(@count $($key),*);
          let mut _set = ::rustc_data_structures::fx::FxHashSet::default();
          let _ = _set.try_reserve(_cap);
          $(
              let _ = _set.insert($key);
          )*
          _set
      }
  };
}
