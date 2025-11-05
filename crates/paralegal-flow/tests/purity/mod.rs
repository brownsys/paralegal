/// This module contains tests for the purity analysis feature. These tests are
/// basically verbatim copies of the tests from scrutinizer.
///
/// many tests have been commented out because paralegal is missing certain
/// features that scrutinizer has.
// Ignored for now because it needs an external crate.
// mod foreign;
mod leaky;
mod misc;
mod raw_ptr;
mod recursive;
mod r#static;
