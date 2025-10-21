/// This module contains tests for the purity analysis feature. These tests are
/// basically verbatim copies of the tests from scrutinizer.
///
/// many tests have been commented out because paralegal is missing certain
/// features that scrutinizer has.
mod r#dyn;
mod fn_ptr;
// Ignored for now because it needs an external crate.
// mod foreign;
mod lam;
mod leaky;
mod raw_ptr;
mod recursive;
mod r#static;
mod structs;
mod vartrack;
