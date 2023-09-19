#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

use parable::{define_flow_test_template, define_test_skip, test_utils::*};

const TEST_CRATE_NAME: &str = "tests/call-chain-analysis-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool =
        run_parable_with_flow_graph_dump_and(TEST_CRATE_NAME, ["--drop-clone"]);
}

macro_rules! define_test {
    ($name:ident: $ctrl:ident -> $block:block) => {
        define_test!($name: $ctrl, $name -> $block);
    };
    ($name:ident: $ctrl:ident, $ctrl_name:ident -> $block:block) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, TEST_CRATE_NAME, $name: $ctrl, $ctrl_name -> $block);
    };
}

define_test!(without_return: ctrl -> {
    let graph = ctrl.graph();
    let src_fn = graph.function("source");
    let src = ctrl.call_site(&src_fn);
    let dest_fn = graph.function("receiver");
    let dest_sink = ctrl.call_site(&dest_fn);
    let dest = dest_sink.input().pop().unwrap();

    assert!(src.flows_to(&dest));
});

define_test!(with_return: ctrl -> {
    let src_fn = ctrl.function("source");
    let src = ctrl.call_site(&src_fn);
    let ctrl = ctrl.ctrl("with_return");
    let dest_fn = ctrl.function("receiver");
    let dest_sink = ctrl.call_site(&dest_fn);
    let dest = dest_sink.input().pop().unwrap();

    assert!(src.flows_to(&dest));
});

define_test!(on_mut_var: ctrl -> {
    let src_fn = ctrl.function("source");
    let src = ctrl.call_site(&src_fn);
    let dest_fn = ctrl.function("receiver");
    let dest_sink = ctrl.call_site(&dest_fn);
    let dest = dest_sink.input().pop().unwrap();

    assert!(src.flows_to(&dest));
});

define_test!(on_mut_var_no_modify: ctrl -> {
    let src_fn = ctrl.function("source");
    if let Some(src) = ctrl.call_sites(&src_fn).pop() {
        let dest_fn = ctrl.function("receiver");
        if let Some(dest_sink) = ctrl.call_sites(&dest_fn).pop() {
            if let Some(dest) = dest_sink.input().pop() {
                assert!(!src.flows_to(&dest));
            }
        }
    }
});

define_test!(field_sensitivity: ctrl -> {
    let produce_usize_fn = ctrl.function("produce_usize");
    let produce_string_fn = ctrl.function("produce_string");
    let consume_usize_fn = ctrl.function("read_usize");
    let consume_string_fn = ctrl.function("read_string");
    let produce_usize = ctrl.call_site(&produce_usize_fn);
    let produce_string = ctrl.call_site(&produce_string_fn);
    let read_string = ctrl.call_site(&consume_string_fn);
    let read_usize = ctrl.call_site(&consume_usize_fn);
    assert!(produce_usize.flows_to(&read_usize.input()[0]));
    assert!(!produce_usize.flows_to(&read_string.input()[0]));
    assert!(produce_string.flows_to(&read_string.input()[0]));
});

define_test_skip!(unused_labels: graph, field_sensitivity -> {
    assert!(graph.has_marker("otherwise_unused"));
});

define_test!(field_sensitivity_across_clone: ctrl -> {
    let produce_usize_fn = ctrl.function("produce_usize");
    let produce_string_fn = ctrl.function("produce_string");
    let consume_usize_fn = ctrl.function("read_usize");
    let consume_string_fn = ctrl.function("read_string");
    let produce_usize = ctrl.call_site(&produce_usize_fn);
    let produce_string = ctrl.call_site(&produce_string_fn);
    let read_string = ctrl.call_site(&consume_string_fn);
    let read_usize = ctrl.call_site(&consume_usize_fn);
    assert!(produce_usize.flows_to(&read_usize.input()[0]));
    assert!(!produce_usize.flows_to(&read_string.input()[0]));
    assert!(produce_string.flows_to(&read_string.input()[0]));
    assert!(!produce_string.flows_to(&read_usize.input()[0]));
});
