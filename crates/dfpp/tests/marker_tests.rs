#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

mod helpers;

use helpers::*;

const TEST_CRATE_NAME: &str = "tests/marker-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool =
        run_dfpp_with_flow_graph_dump_and(TEST_CRATE_NAME, ["--no-cross-function-analysis"]);
}

macro_rules! define_test {
    ($name:ident: $ctrl:ident -> $block:block) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, TEST_CRATE_NAME, $name: $ctrl, $name -> $block);
    };
}

define_test!(use_wrapper: ctrl -> {
    let uwf = ctrl.function("make_wrapper");
    let cs = ctrl.call_site(&uwf);
    assert!(ctrl.types_for(&dfpp::desc::DataSource::FunctionCall(cs.call_site().clone()))
        .expect("Type not found on method")
        .iter().any(|t| t.as_str().strip_prefix("Wrapper").is_some()))
});
