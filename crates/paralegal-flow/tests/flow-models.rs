#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

use paralegal_flow::{define_flow_test_template, test_utils::*};
use paralegal_spdg::Identifier;

const TEST_CRATE_NAME: &str = "tests/flow-models";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump(TEST_CRATE_NAME);
}

macro_rules! define_test {
    ($($t:tt)*) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, TEST_CRATE_NAME, $($t)*);
    };
}

define_test!(thread_spawn: graph -> {
    let src = graph.marked(Identifier::new_intern("source"));
    let pass = graph.marked(Identifier::new_intern("pass"));
    let target = graph.marked(Identifier::new_intern("target"));

    assert!(!src.is_empty());
    assert!(!pass.is_empty());
    assert!(!target.is_empty());

    assert!(src.flows_to_data(&pass));
    assert!(pass.flows_to_data(&target));
});
