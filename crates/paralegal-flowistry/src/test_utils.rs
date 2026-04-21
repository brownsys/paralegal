//! Test helpers for paralegal-flowistry unit tests.

#![allow(missing_docs)]

use paralegal_rustc_utils::{mir::borrowck_facts, test_utils};
use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_hir::BodyId;
use rustc_middle::ty::TyCtxt;

pub fn compile_body(
  input: &str,
  callback: impl for<'tcx> FnOnce(TyCtxt<'tcx>, BodyId, &'tcx BodyWithBorrowckFacts<'tcx>)
    + Send,
) {
  borrowck_facts::enable_mir_simplification();
  test_utils::compile_body(input, callback)
}
