#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use paralegal_flow::test_utils::*;

const CRATE_DIR: &str = "tests/cross-crate";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump(CRATE_DIR);
}

macro_rules! define_test {
    ($name:ident: $ctrl:ident -> $block:block) => {
        define_test!($name: $ctrl, $name -> $block);
    };
    ($name:ident: $ctrl:ident, $ctrl_name:ident -> $block:block) => {
        paralegal_flow::define_flow_test_template!(TEST_CRATE_ANALYZED, CRATE_DIR, $name: $ctrl, $ctrl_name -> $block);
    };
}

define_test!(basic : graph -> {
    let src_fn = graph.function("src");
    let src = graph.call_site(&src_fn);
    let not_src_fn = graph.function("not_src");
    let not_src = graph.call_site(&not_src_fn);
    let target_fn = graph.function("target");
    let target = graph.call_site(&target_fn);
    assert!(src.output().flows_to_data(&target.input()));
    assert!(!not_src.output().flows_to_data(&target.input()));
});
