#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use paralegal_flow::test_utils::*;
use paralegal_spdg::Identifier;

const CRATE_DIR: &str = "tests/boxes";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump_and(
        CRATE_DIR,
        ["--local-crate-only", "--no-adaptive-approximation"]
    );
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

define_test!(ref_with_checkpoint: graph -> {
    let sources = graph.marked(Identifier::new_intern("source"));
    let mid = graph.marked(Identifier::new_intern("checkpoint_2"));
    let end = graph.marked(Identifier::new_intern("sink"));
    let modifier = graph.marked(Identifier::new_intern("modifier"));
    assert!(!sources.is_empty());
    assert!(!mid.is_empty());
    assert!(!end.is_empty());
    assert!(!modifier.is_empty());
    assert!(modifier.flows_to_data(&end));
    assert!(sources.flows_to_data(&end));
    assert!(!mid.always_happens_before_data(&modifier, &end));
});

// This one is just to check that fields have the same behavior as boxes.
define_test!(field_ref: graph -> {
    let sources = graph.marked(Identifier::new_intern("source_2"));
    let end = graph.marked(Identifier::new_intern("sink"));
    let modifier = graph.marked(Identifier::new_intern("modifier"));
    assert!(!sources.is_empty());
    assert!(!end.is_empty());
    assert!(!modifier.is_empty());
    assert!(modifier.flows_to_data(&end));
    assert!(sources.flows_to_data(&end));
    assert!(!sources.always_happens_before_data(&modifier, &end));
});

define_test!(ref_mut_box: graph -> {
    let sources = graph.marked(Identifier::new_intern("source_2"));
    let end = graph.marked(Identifier::new_intern("sink"));
    let modifier = graph.marked(Identifier::new_intern("modifier"));
    assert!(!sources.is_empty());
    assert!(!end.is_empty());
    assert!(!modifier.is_empty());
    assert!(modifier.flows_to_data(&end));
    assert!(sources.flows_to_data(&end));
    assert!(!sources.always_happens_before_data(&modifier, &end));
});

define_test!(box_ref_mut: graph -> {
    let sources = graph.marked(Identifier::new_intern("source_2"));
    let end = graph.marked(Identifier::new_intern("sink"));
    let modifier = graph.marked(Identifier::new_intern("modifier"));
    assert!(!sources.is_empty());
    assert!(!end.is_empty());
    assert!(!modifier.is_empty());
    assert!(modifier.flows_to_data(&end));
    assert!(sources.flows_to_data(&end));
    assert!(!sources.always_happens_before_data(&modifier, &end));
});

define_test!(strong_box_update skip "Box modification is not currently considered strong. See https://github.com/brownsys/paralegal/issues/155": graph -> {
    let sources = graph.marked(Identifier::new_intern("source_2"));
    let end = graph.marked(Identifier::new_intern("sink"));
    let modifier = graph.marked(Identifier::new_intern("modifier"));
    assert!(!sources.is_empty());
    assert!(!end.is_empty());
    assert!(!modifier.is_empty());
    assert!(modifier.flows_to_data(&end));
    assert!(!sources.flows_to_data(&end));
    //assert!(!sources.always_happens_before_data(&modifier, &end));
});

define_test!(strong_ref_in_box_update: graph -> {
    let sources = graph.marked(Identifier::new_intern("source_2"));
    let end = graph.marked(Identifier::new_intern("sink"));
    let modifier = graph.marked(Identifier::new_intern("modifier"));
    assert!(!sources.is_empty());
    assert!(!end.is_empty());
    assert!(!modifier.is_empty());
    assert!(modifier.flows_to_data(&end));
    assert!(!sources.flows_to_data(&end));
    //assert!(!sources.always_happens_before_data(&modifier, &end));
});
