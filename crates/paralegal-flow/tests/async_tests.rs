#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use paralegal_flow::{define_test_skip, test_utils::*};

const CRATE_DIR: &str = "tests/async-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool =
        run_paralegal_flow_with_flow_graph_dump_and(CRATE_DIR, ["--drop-poll"]);
}

macro_rules! define_test {
    ($name:ident: $ctrl:ident -> $block:block) => {
        define_test!($name: $ctrl, $name -> $block);
    };
    ($name:ident: $ctrl:ident, $ctrl_name:ident -> $block:block) => {
        paralegal_flow::define_flow_test_template!(TEST_CRATE_ANALYZED, CRATE_DIR, $name: $ctrl, $ctrl_name -> $block);
    };
}

define_test!(top_level_inlining_happens : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let dp_fn = graph.function("dp_user_data");
    let dp = graph.call_site(&dp_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);

    assert!(get.output().flows_to_data(&dp.input()));
    assert!(dp.output().flows_to_data(&send.input()));
    assert!(get.output().flows_to_data(&send.input()));
    assert!(!get.output().is_neighbor_data(&send.input()))
});

define_test!(awaiting_works : graph -> {
    let get_fn = graph.function("async_get_user_data");
    let get = graph.call_site(&get_fn);
    let dp_fn = graph.function("async_dp_user_data");
    let dp = graph.call_site(&dp_fn);
    let send_fn = graph.function("async_send_user_data");
    let send = graph.call_site(&send_fn);

    assert!(get.output().flows_to_data(&dp.input()));
    assert!(dp.output().flows_to_data(&send.input()));
    assert!(get.output().flows_to_data(&send.input()));
    assert!(!get.output().is_neighbor_data(&send.input()))
});

define_test!(two_data_over_boundary : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let get2_fn = graph.function("get_user_data2");
    let get2 = graph.call_site(&get2_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);
    let send2_fn = graph.function("send_user_data2");
    let send2 = graph.call_site(&send2_fn);

    assert!(get.output().flows_to_data(&send.input()));
    assert!(get2.output().flows_to_data(&send2.input()));
    assert!(!get.output().flows_to_data(&send2.input()));
    assert!(!get2.output().flows_to_data(&send.input()));
});

define_test!(inlining_crate_local_async_fns: graph -> {

    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let dp_fn = graph.function("dp_user_data");
    let dp = graph.call_site(&dp_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);

    assert!(get.output().flows_to_data(&dp.input()));
    assert!(dp.output().flows_to_data(&send.input()));
    assert!(get.output().flows_to_data(&send.input()));
    assert!(!get.output().is_neighbor_data(&send.input()))
});

define_test_skip!(arguments_work "arguments are not emitted properly in the graph data structure the test is defined over, making the test fail. When I manually inspected the (visual) graph dump this test case seemed to be correct." : graph -> {
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);
    let data = graph.argument(graph.ctrl(), 0);
    assert!(graph.connects_data((data, send.1), send));
});

define_test!(no_inlining_overtaint
    :
    graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let get2_fn = graph.function("get_user_data2");
    let get2 = graph.call_site(&get2_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);
    let send2_fn = graph.function("send_user_data2");
    let send2 = graph.call_site(&send2_fn);
    let dp_fn = graph.function("dp_user_data");
    let dp = graph.call_site(&dp_fn);

    assert!(get.output().flows_to_data(&send.input()));
    assert!(get2.output().flows_to_data(&send2.input()));
    assert!(get2.output().flows_to_data(&dp.input()));
    assert!(!get.output().flows_to_data(&dp.input()));

    assert!(!get.output().flows_to_data(&send2.input()));
    assert!(!get2.output().flows_to_data(&send.input()));
});

define_test!(no_immutable_inlining_overtaint : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let get2_fn = graph.function("get_user_data2");
    let get2 = graph.call_site(&get2_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);
    let send2_fn = graph.function("send_user_data2");
    let send2 = graph.call_site(&send2_fn);

    assert!(get.output().flows_to_data(&send.input()));
    assert!(get2.output().flows_to_data(&send2.input()));
    assert!(!get.output().flows_to_data(&send2.input()));
    assert!(!get2.output().flows_to_data(&send.input()));
});

define_test!(remove_poll_match: graph -> {
    let input_fn = graph.function("some_input");
    let input = graph.call_site(&input_fn);
    let target_fn = graph.function("target");
    let target = graph.call_site(&target_fn);
    let poll_fn = graph.function("poll");
    let poll = graph.call_site(&poll_fn);
    let new_unchecked_fn = graph.function("new_unchecked");
    let new_unchecked = graph.call_site(&new_unchecked_fn);
    let get_context_fn = graph.function("get_context");
    let get_context = graph.call_site(&get_context_fn);
    let into_future_fn = graph.function("into_future");
    let into_future = graph.call_site(&into_future_fn);
    let _f_fn = graph.function("f");
    let _f = graph.call_site(&_f_fn);
    assert!(input.output().flows_to_data(&target.input()));

    assert!(poll.output().is_terminal());
    assert!(new_unchecked.output().is_terminal());
    assert!(get_context.output().is_terminal());
    assert!(into_future.output().is_terminal());
});

define_test!(no_overtaint_over_poll: graph -> {
    let input_fn = graph.function("some_input");
    let input = graph.call_site(&input_fn);
    let another_input_fn = graph.function("another_input");
    let another_input = graph.call_site(&another_input_fn);

    let target_fn = graph.function("target");
    let target = graph.call_site(&target_fn);
    let another_target_fn = graph.function("another_target");
    let another_target = graph.call_site(&another_target_fn);

    assert!(input.output().flows_to_data(&target.input()));
    assert!(another_input.output().flows_to_data(&another_target.input()));
    assert!(!input.output().flows_to_data(&another_target.input()));
    assert!(!another_input.output().flows_to_data(&target.input()));
});

define_test!(return_from_async: graph -> {
    let input_fn = graph.function("some_input");
    let input = graph.call_site(&input_fn);
    assert!(graph.returns(&input.output()))
});

define_test!(async_return_from_async: graph -> {
    let input_fn = graph.function("some_input");
    let input = graph.call_site(&input_fn);
    assert!(graph.returns(&input.output()))
});
