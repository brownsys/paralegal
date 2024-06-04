#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use paralegal_flow::test_utils::*;
use paralegal_spdg::Identifier;

const CRATE_DIR: &str = "tests/boxes";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump(CRATE_DIR);
}

macro_rules! define_test {
    ($($t:tt)*) => {
        paralegal_flow::define_flow_test_template!(TEST_CRATE_ANALYZED, CRATE_DIR, $($t)*);
    };
}

define_test!(simple_overtaint: graph -> {
    let sources = graph.marked(Identifier::new_intern("source"));
    let mid = graph.marked(Identifier::new_intern("checkpoint"));
    let end = graph.marked(Identifier::new_intern("sink"));
    assert!(!sources.is_empty());
    assert!(!mid.is_empty());
    assert!(!end.is_empty());
    assert!(sources.always_happens_before_data(&mid, &end));
});

define_test!(box_mut_ref: graph -> {
    let sources = graph.marked(Identifier::new_intern("source"));
    let mid = graph.marked(Identifier::new_intern("checkpoint_2"));
    let end = graph.marked(Identifier::new_intern("sink"));
    let modifier = graph.marked(Identifier::new_intern("modifier"));
    assert!(!sources.is_empty());
    assert!(!mid.is_empty());
    assert!(!end.is_empty());
    assert!(!modifier.is_empty());
    assert!(modifier.flows_to_data(&end));
    assert!(end.flows_to_data(&end));
});

define_test!(field_ref: graph -> {
    let sources = graph.marked(Identifier::new_intern("source_2"));
    let end = graph.marked(Identifier::new_intern("sink"));
    let modifier = graph.marked(Identifier::new_intern("modifier"));
    assert!(!sources.is_empty());
    assert!(!end.is_empty());
    assert!(!modifier.is_empty());
    assert!(modifier.flows_to_data(&end));
    assert!(end.flows_to_data(&end));
});

define_test!(simple_box_mut_ref: graph -> {
    let sources = graph.marked(Identifier::new_intern("source_2"));
    let end = graph.marked(Identifier::new_intern("sink"));
    let modifier = graph.marked(Identifier::new_intern("modifier"));
    assert!(!sources.is_empty());
    assert!(!end.is_empty());
    assert!(!modifier.is_empty());
    assert!(modifier.flows_to_data(&end));
    assert!(end.flows_to_data(&end));
});
