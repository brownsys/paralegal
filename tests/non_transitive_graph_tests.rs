#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use dfpp::Symbol;
mod helpers;
use helpers::*;

const CRATE_DIR: &str = "tests/non-transitive-graph-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = *helpers::DFPP_INSTALLED
        && with_current_directory(CRATE_DIR, || { run_dfpp_with_graph_dump_and(["--no-cross-function-analysis"]) }).map_or_else(
            |e| {
                println!("io err {}", e);
                false
            },
            |t| t
        );
}

macro_rules! define_test {
    ($name:ident : $graph:ident -> $block:block) => {
        define_G_test_template!(TEST_CRATE_ANALYZED, CRATE_DIR, $name : $graph -> $block);
    };
}

define_test!(return_is_tracked : graph -> {
    let get = graph.function_call("input");
    let send = graph.function_call("output");

    assert!(graph.returns_direct(&send));
    assert!(graph.returns(&get));
});

define_test!(simple_happens_before_has_connections: graph -> {
    let get = graph.function_call("get_user_data");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &dp));
    assert!(graph.connects(&dp, &send));
    assert!(graph.connects(&get, &send));
    assert!(!graph.connects_direct(&get, &send))
});

define_test!(happens_before_if_has_connections : graph -> {
    let get = graph.function_call("get_user_data");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");
    assert!(graph.connects(&get, &dp,));
    assert!(graph.connects(&dp, &send));
    assert!(graph.connects_direct(&get, &send));
});

define_test!(data_influenced_conditional_happens_before: graph -> {
    let get = graph.function_call("get_user_data");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");
    assert!(graph.connects(&get, &dp,));
    assert!(graph.connects(&dp, &send));
    assert!(graph.connects_direct(&get, &send));
});

define_test!(conditional_happens_before_with_two_parents_before_if: graph -> {
    let get = graph.function_call("get_user_data_with");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");
    let push = graph.function_call("push");
    assert!(graph.connects(&push, &get));
    assert!(graph.connects(&get, &dp));
    assert!(graph.connects(&dp, &send));
    assert!(graph.connects_direct(&get, &send));
    assert!(!graph.connects_direct(&push, &send));
    assert!(!graph.connects_direct(&push, &dp));
});

define_test!(loops : graph -> {
    let get = graph.function_call("get_user_data");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");
    assert!(graph.connects(&get, &dp,));
    assert!(graph.connects(&dp, &send));
    assert!(graph.connects_direct(&get, &send));
});

define_test!(loop_retains_dependency : graph -> {
    let get = graph.function_call("get_user_data");
    let get_other = graph.function_call("get_other_data");
    let dp = graph.function_call("dp_user_data");
    let modify_other = graph.function_call("modify_other_data");
    let send = graph.function_call("send_user_data");
    assert!(graph.connects(&get, &dp));
    assert!(graph.connects(&get_other, &dp));
    assert!(graph.connects(&modify_other, &dp));
    assert!(graph.connects(&dp, &send));
    assert!(graph.connects(&modify_other, &send));
    assert!(graph.connects_direct(&get, &send));
});

define_test_skip!(arguments : graph -> {
    let body_id = *graph.body.0.keys().next().unwrap();
    let a1 = graph.argument(body_id, 0);

    let dp = graph.function_call("dp_user_data");

    assert!(graph.connects(&(a1, body_id), &dp));
});

define_test!(modify_pointer : graph -> {
    let get = graph.function_call("get_user_data");
    let create = graph.function_call("modify_vec");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &create));
    assert!(graph.connects(&create, &send));
    assert!(graph.connects(&get, &send));
});

define_test!(on_mut_var : graph -> {
    let source = graph.function_call("source");
    let modify = graph.function_call("modify_it");
    let receive = graph.function_call("receiver");

    assert!(graph.connects(&source, &modify));
    assert!(graph.connects(&modify, &receive));
});

define_test!(spurious_connections_in_deref: graph -> {
    let source = &graph.function_call("new_s");
    let modify = &graph.function_call("deref");
    let receive = &graph.function_call("read_t");
    assert!(graph.connects_direct(source, modify));
    assert!(graph.connects_direct(modify, receive));
    assert!(!graph.connects_direct(source, receive));
    assert!(graph.connects(source, receive));
});
