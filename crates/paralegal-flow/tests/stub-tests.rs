//! These tests check that replacement models work.
//!
//! At the moment it only checks that replacing `std::thread::spawn(f)` being
//! replaced by `f()` and analogous for `tokio::spawn` works.

#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

use paralegal_flow::{define_flow_test_template, test_utils::*};
use paralegal_spdg::Identifier;

const TEST_CRATE_NAME: &str = "tests/stub-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump_and(
        TEST_CRATE_NAME,
        ["--include=crate", "--no-adaptive-approximation"]
    );
}

macro_rules! define_test {
    ($($t:tt)*) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, TEST_CRATE_NAME, $($t)*);
    };
}

fn check_source_pass_target(graph: CtrlRef<'_>) {
    let src = graph.marked(Identifier::new_intern("source"));
    let pass = graph.marked(Identifier::new_intern("pass"));
    let target = graph.marked(Identifier::new_intern("target"));

    assert!(!src.is_empty());
    assert!(!pass.is_empty());
    assert!(!target.is_empty());

    assert!(src.flows_to_data(&pass));
    assert!(pass.flows_to_data(&target));
}

define_test!(thread_spawn: graph -> {
    check_source_pass_target(graph);
});

define_test!(marked_thread_spawn: graph -> {
    simple_source_target_flow(graph);
});

define_test!(async_spawn: graph -> {
    check_source_pass_target(graph);
});

define_test!(marked_async_spawn: graph -> {
    simple_source_target_flow(graph);
});

define_test!(blocking_with_marker: graph -> {
    simple_source_target_flow(graph);
});

define_test!(marked_blocking_like: graph -> {
    simple_source_target_flow(graph);
});

define_test!(test_blocking_like: graph -> {
    simple_source_target_flow(graph);
});

fn simple_source_target_flow(graph: CtrlRef<'_>) {
    let src = graph.marked(Identifier::new_intern("source"));
    let target = graph.marked(Identifier::new_intern("target"));

    assert!(!src.is_empty());
    assert!(!target.is_empty());

    assert!(src.flows_to_data(&target));
}

define_test!(block_fn: graph -> {
    simple_source_target_flow(graph)
});

define_test!(test_blocking_with_let_bound_closure: graph -> {
    simple_source_target_flow(graph)
});

define_test!(block_closure: graph -> {
    simple_source_target_flow(graph)
});

define_test!(strategic_overtaint: graph -> {
    simple_source_target_flow(graph)
});

define_test!(strategic_overtaint_2: graph -> {
    simple_source_target_flow(graph)
});

define_test!(no_taint_without_connection: graph -> {

    let src = graph.marked(Identifier::new_intern("source"));
    let target = graph.marked(Identifier::new_intern("target"));

    assert!(!src.is_empty());
    assert!(!target.is_empty());

    assert!(!src.flows_to_data(&target));
});
