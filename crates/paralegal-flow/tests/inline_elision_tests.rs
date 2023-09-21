#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use paralegal_flow::{define_G_test_template, define_test_skip, test_utils::*, Symbol};

const CRATE_DIR: &str = "tests/inline-elision-tests";

const TARGET_FN: &str = "std::convert::identity";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool =
        run_paralegal_flow_with_graph_dump_and(CRATE_DIR, ["--inline-elision"]);
}

macro_rules! define_test {
    ($name:ident :  $graph:ident -> $block:block) => {
        define_G_test_template!(TEST_CRATE_ANALYZED, CRATE_DIR, $name : $graph -> $block);
    };
}

define_test!(basic_elision : graph -> {
    let input = graph.function_call("input");
    let receiver = graph.function_call("receive_touched");
    assert!(graph.function_calls(TARGET_FN).is_empty() || graph.connects_none(&graph.function_call(TARGET_FN)));
    assert!(graph.connects(&input, &receiver))

});

define_test!(basic_elision_mut : graph -> {
    let input = graph.function_call("input");
    let receiver = graph.function_call("receive_touched");
    assert!(graph.function_calls(TARGET_FN).is_empty() || graph.connects_none(&graph.function_call(TARGET_FN)));
    assert!(graph.connects(&input, &receiver))

});

define_test!(unelision: graph -> {
    graph.function_call("other_input");
});

define_test_skip!(connection_precision: graph -> {
    let touched = graph.function_call(" input");
    let untouched = graph.function_call("other_input");

    let receive_touched = graph.function_call("receive_touched");
    let receive_untouched = graph.function_call("receive_untouched");
    assert!(graph.connects(&touched, &receive_touched));
    assert!(graph.connects(&untouched, &receive_untouched));
    assert!(!graph.connects(&touched, &receive_untouched));
    assert!(!graph.connects(&untouched, &receive_touched))
});

define_test_skip!(connection_precision_2: graph -> {
    let touched = graph.function_call(" input");
    let untouched = graph.function_call("other_input");
    let receive_touched = graph.function_call("receive_touched");
    let receive_untouched = graph.function_call("receive_untouched");
    assert!(graph.connects(&touched, &receive_touched));
    assert!(graph.connects(&untouched, &receive_untouched));
    assert!(!graph.connects(&touched, &receive_untouched));
    assert!(!graph.connects(&untouched, &receive_touched))
});

define_test_skip!(connection_precision_3: graph -> {
    let touched = graph.function_call(" input");
    let untouched = graph.function_call("other_input");
    let receive_touched = graph.function_call("receive_touched");
    let receive_untouched = graph.function_call("receive_untouched");
    assert!(graph.connects(&touched, &receive_touched));
    assert!(graph.connects(&untouched, &receive_untouched));
    assert!(!graph.connects(&touched, &receive_untouched));
    assert!(!graph.connects(&untouched, &receive_touched))
});
define_test!(connection_precision_self: graph -> {
    let touched = graph.function_call(" input");
    let untouched = graph.function_call("other_input");
    let receive_touched = graph.function_call("receive_touched");
    let receive_untouched = graph.function_call("receive_untouched");
    assert!(graph.connects(&touched, &receive_touched));
    assert!(graph.connects(&untouched, &receive_untouched));
    assert!(!graph.connects(&touched, &receive_untouched));
    assert!(graph.connects(&untouched, &receive_touched))
});

define_test!(connection_precision_args: graph -> {
    let touched = graph.function_call(" input");
    let untouched = graph.function_call("other_input");
    let receive_touched = graph.function_call("receive_touched");
    let receive_untouched = graph.function_call("receive_untouched");
    assert!(graph.connects(&touched, &receive_touched));
    assert!(graph.connects(&untouched, &receive_untouched));
    assert!(!graph.connects(&touched, &receive_untouched));
    assert!(!graph.connects(&untouched, &receive_touched))
});

define_test_skip!(no_elision_without_input "suspended because semantics of how suspected side effecting functions should be handled is unclear." : graph -> {
    let input = graph.function_call("inner");
    let output = graph.function_call("receive_touched");

    assert!(graph.connects(&input, &output));
});

define_test_skip!(no_elision_without_output "suspended because semantics of how suspected side effecting functions should be handled is unclear." : graph -> {
    let input = graph.function_call("input");
    let output = graph.function_call("do_io");

    assert!(graph.connects(&input, &output));
});
