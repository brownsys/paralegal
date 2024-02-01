#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use indexical::ToIndex;
use paralegal_flow::{test_utils::*, Symbol};

const CRATE_DIR: &str = "tests/control-flow-tests";

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

define_test!(process_basic : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let check_fn = graph.function("check_user_data");
    let check = graph.call_site(&check_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);

    assert!(get.output().flows_to_data(&check.input()));
    assert!(!check.output().flows_to_data(&send.input()));
    assert!(get.output().flows_to_data(&send.input()));
    assert!(get.output().never_happens_before_data(&check.input(), &send.input()));
});

define_test!(process_if : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let check_fn = graph.function("check_user_data");
    let check = graph.call_site(&check_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);

    assert!(get.output().flows_to_data(&check.input()));
    assert!(get.output().flows_to_data(&send.input()));
    assert!(check.output().influences_next_control(&send.input()));
});

define_test!(process_if_after : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let check_fn = graph.function("check_user_data");
    let check = graph.call_site(&check_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);
    let modify_fn = graph.function("modify");
    let modify = graph.call_site(&modify_fn);

    assert!(get.output().flows_to_data(&check.input()));
    assert!(check.output().influences_next_control(&modify.input()));
    assert!(modify.output().flows_to_data(&send.input()));
    assert!(!check.output().influences_next_control(&send.input()));
});

define_test!(process_nested_if : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let check_fn = graph.function("check_user_data");
    let check = graph.call_site(&check_fn);
    let check2_fn = graph.function("check2");
    let check2 = graph.call_site(&check2_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);

    assert!(get.output().flows_to_data(&check.input()));
    assert!(get.output().flows_to_data(&check2.input()));
    assert!(get.output().flows_to_data(&send.input()));
    assert!(check.output().influences_next_control(&check2.input()));
    assert!(check2.output().influences_next_control(&send.input()));
});

define_test!(process_if_multiple_statements : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let check_fn = graph.function("check_user_data");
    let check = graph.call_site(&check_fn);
    let modify_fn = graph.function("modify");
    let modify = graph.call_site(&modify_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);

    assert!(get.output().flows_to_data(&check.input()));
    assert!(get.output().flows_to_data(&modify.input()));
    assert!(modify.output().flows_to_data(&send.input()));
    assert!(check.output().influences_next_control(&modify.input()));
    assert!(check.output().influences_next_control(&send.input()));
    assert!(!modify.output().influences_next_control(&send.input()));
});

define_test!(process_if_not_function_call : graph -> {
    let getx_fn = graph.function("get_x");
    let getx = graph.call_site(&getx_fn);
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let modify_fn = graph.function("modify");
    let modify = graph.call_site(&modify_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);

    assert!(!getx.output().flows_to_data(&get.input()));
    assert!(getx.output().influences_next_control(&modify.input()));
    assert!(modify.output().flows_to_data(&send.input()));
    assert!(!getx.output().influences_next_control(&send.input()));
});

define_test!(process_no_args : graph -> {
    let getx_fn = graph.function("get_x");
    let getx = graph.call_site(&getx_fn);
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);

    assert!(getx.output().flows_to_any(&get.output()));
    assert!(get.output().flows_to_data(&send.input()));
    assert!(getx.output().flows_to_any(&send.input()));
    assert!(getx.output().influences_next_control(&get.output()));
});
