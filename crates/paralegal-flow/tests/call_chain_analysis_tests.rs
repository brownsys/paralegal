#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

use paralegal_flow::{define_flow_test_template, test_utils::*};

const TEST_CRATE_NAME: &str = "tests/call-chain-analysis-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump(TEST_CRATE_NAME);
}

macro_rules! define_test {
    ($($t:tt)*) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, TEST_CRATE_NAME, $($t)*);
    };
}

define_test!(without_return: ctrl -> {
    let graph = ctrl.graph();
    let src_fn = graph.function("source");
    let src = ctrl.call_site(&src_fn);
    let dest_fn = graph.function("receiver");
    let dest_sink = ctrl.call_site(&dest_fn);
    let dest = dest_sink.input().nth(0).unwrap();

    assert!(src.output().flows_to_data(&dest));
});

define_test!(with_return: ctrl -> {
    let src_fn = ctrl.function("source");
    let src = ctrl.call_site(&src_fn);
    let ctrl = ctrl.ctrl("with_return");
    let dest_fn = ctrl.function("receiver");
    let dest_sink = ctrl.call_site(&dest_fn);
    let dest = dest_sink.input().nth(0).unwrap();

    assert!(src.output().flows_to_data(&dest));
});

define_test!(on_mut_var: ctrl -> {
    let src_fn = ctrl.function("source");
    let src = ctrl.call_site(&src_fn);
    let dest_fn = ctrl.function("receiver");
    let dest_sink = ctrl.call_site(&dest_fn);
    let dest = dest_sink.input().nth(0).unwrap();

    assert!(src.output().flows_to_data(&dest));
});

define_test!(on_mut_var_no_modify: ctrl -> {
    let src_fn = ctrl.function("source");
    if let Some(src) = ctrl.call_sites(&src_fn).pop() {
        let dest_fn = ctrl.function("receiver");
        if let Some(dest_sink) = ctrl.call_sites(&dest_fn).pop() {
            assert!(!src.output().flows_to_data(&dest_sink.input()));
        }
    }
});

define_test!(field_sensitivity: ctrl -> {
    // Tests that when we stuff two piece of data into a struct
    // they are tracked separately and if we pull them back out they
    // are independent.
    //
    // I'm sorry for how elaborate this test case is.
    // The machinery here is just to distinguish the "used"
    // and "unused" "read_usize" call sites.
    let produce_usize_fn = ctrl.function("produce_usize");
    let produce_string_fn = ctrl.function("produce_string");
    let consume_usize_fn = ctrl.function("read_usize");
    let consume_string_fn = ctrl.function("read_string");
    let produce_usize = ctrl.call_site(&produce_usize_fn);
    let produce_string = ctrl.call_site(&produce_string_fn);
    let read_string = ctrl.call_site(&consume_string_fn);
    let read_usizes = ctrl.call_sites(&consume_usize_fn);

    #[derive(Eq, PartialEq, Copy, Clone)]
    enum CallSiteState {
        Unknow, Distraction, Checked
    }

    use CallSiteState::*;

    let mut usize_call_sites = [Unknow;2];
    for (idx, read_usize) in read_usizes.iter().enumerate() {
        usize_call_sites[idx] = if produce_usize.output().flows_to_data(&read_usize.input()) {
            Checked
        } else {
            Distraction
        };
    }
    assert!(!produce_usize.output().flows_to_data(&read_string.input()));
    assert!(produce_string.output().flows_to_data(&read_string.input()));
    assert!(usize_call_sites.contains(&Distraction));
    assert!(usize_call_sites.contains(&Checked));
});

define_test!(unused_labels skip "": graph, field_sensitivity -> {
    assert!(graph.has_marker("otherwise_unused"));
});

define_test!(field_sensitivity_across_clone: ctrl -> {
    // Tests that when we stuff two piece of data into a struct
    // they are tracked separately and if we pull them back out they
    // are independent, even if the data structure is "clone()"d in
    // between.
    //
    // Similar to the "field_sensitivity" test case.
    //
    // I'm sorry for how elaborate this test case is.
    // The machinery here is just to distinguish the "used"
    // and "unused" "read_usize" call sites.
    let produce_usize_fn = ctrl.function("produce_usize");
    let produce_string_fn = ctrl.function("produce_string");
    let consume_usize_fn = ctrl.function("read_usize");
    let consume_string_fn = ctrl.function("read_string");
    let produce_usize = ctrl.call_site(&produce_usize_fn);
    let produce_string = ctrl.call_site(&produce_string_fn);
    let read_string = ctrl.call_site(&consume_string_fn);
    let read_usizes = ctrl.call_sites(&consume_usize_fn);

    #[derive(Eq, PartialEq, Copy, Clone)]
    enum CallSiteState {
        Unknow, Distraction, Checked
    }

    use CallSiteState::*;

    let mut usize_call_sites = [Unknow;2];
    for (idx, read_usize) in read_usizes.iter().enumerate() {
        usize_call_sites[idx] = if produce_usize.output().flows_to_data(&read_usize.input()) {
            assert!(!produce_string.output().flows_to_data(&read_usize.input()));
            Checked
        } else {
            Distraction
        };
    }
    assert!(!produce_usize.output().flows_to_data(&read_string.input()));
    assert!(produce_string.output().flows_to_data(&read_string.input()));
});

define_test!(no_overtaint_over_fn_call
    skip
    "Field level precision across function calls is broken.
    See https://github.com/willcrichton/flowistry/issues/94."
    : graph -> {
    let input_fn = graph.function("input");
    let input = graph.call_site(&input_fn);
    let another_input_fn = graph.function("source");
    let another_input = graph.call_site(&another_input_fn);

    let target_fn = graph.function("target");
    let target = graph.call_site(&target_fn);
    let another_target_fn = graph.function("another_target");
    let another_target = graph.call_site(&another_target_fn);

    assert!(input.output().flows_to_data(&target.input()));
    assert!(another_input.output().flows_to_data(&another_target.input()));
    assert!(!dbg!(input.output()).flows_to_data(&dbg!(another_target.input())));
    assert!(!another_input.output().flows_to_data(&target.input()));
});

define_test!(no_overtaint_over_generic_fn_call
    skip
    "Field level precision across function calls is broken.
    See https://github.com/willcrichton/flowistry/issues/94."
    : graph -> {
    let input_fn = graph.function("input");
    let input = graph.call_site(&input_fn);
    let another_input_fn = graph.function("source");
    let another_input = graph.call_site(&another_input_fn);

    let target_fn = graph.function("target");
    let target = graph.call_site(&target_fn);
    let another_target_fn = graph.function("another_target");
    let another_target = graph.call_site(&another_target_fn);

    assert!(input.output().flows_to_data(&target.input()));
    assert!(another_input.output().flows_to_data(&another_target.input()));
    assert!(!dbg!(input.output()).flows_to_data(&dbg!(another_target.input())));
    assert!(!another_input.output().flows_to_data(&target.input()));
});

define_test!(no_overtaint_over_nested_fn_call
    skip
    "Field level precision across function calls is broken.
    See https://github.com/willcrichton/flowistry/issues/94."
    : graph -> {
    let input_fn = graph.function("input");
    let input = graph.call_site(&input_fn);
    let another_input_fn = graph.function("source");
    let another_input = graph.call_site(&another_input_fn);

    let target_fn = graph.function("target");
    let target = graph.call_site(&target_fn);
    let another_target_fn = graph.function("another_target");
    let another_target = graph.call_site(&another_target_fn);

    assert!(input.output().flows_to_data(&target.input()));
    assert!(another_input.output().flows_to_data(&another_target.input()));
    assert!(!dbg!(input.output()).flows_to_data(&dbg!(another_target.input())));
    assert!(!another_input.output().flows_to_data(&target.input()));

});
