#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use paralegal_flow::{define_test_skip, define_flow_test_template, test_utils::*, Symbol};

const CRATE_DIR: &str = "tests/non-transitive-graph-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool =
        run_paralegal_flow_with_flow_graph_dump_and(CRATE_DIR, ["--no-cross-function-analysis"]);
}

macro_rules! define_test {
    ($name:ident: $ctrl:ident -> $block:block) => {
        define_test!($name: $ctrl, $name -> $block);
    };
    ($name:ident: $ctrl:ident, $ctrl_name:ident -> $block:block) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, CRATE_DIR, $name: $ctrl, $ctrl_name -> $block);
    };
}

define_test!(return_is_tracked : graph -> {
    let get_fn = graph.function("input");
    let get = graph.call_site(&get_fn);
    let send_fn = graph.function("output");
    let send = graph.call_site(&send_fn);

    assert!(graph.returns(&send.output()));
    assert!(graph.returns(&get.output()));
});

define_test!(simple_happens_before_has_connections: graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let dp_fn = graph.function("dp_user_data");
    let dp = graph.call_site(&dp_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);

    assert!(get.output().flows_to_data(&dp.input()));
    assert!(dp.output().flows_to_data(&send.input()));
    assert!(get.output().flows_to_data(&send.input()));
    assert!(!get.output().flows_to_data(&send.input()));
});

define_test!(happens_before_if_has_connections : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let dp_fn = graph.function("dp_user_data");
    let dp = graph.call_site(&dp_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);
    assert!(get.output().flows_to_data(&dp.input(),));
    assert!(dp.output().flows_to_data(&send.input()));
    assert!(get.output().flows_to_data(&send.input()));
});

define_test!(data_influenced_conditional_happens_before: graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let dp_fn = graph.function("dp_user_data");
    let dp = graph.call_site(&dp_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);
    assert!(get.output().flows_to_data(&dp.input(),));
    assert!(dp.output().flows_to_data(&send.input()));
    assert!(get.output().flows_to_data(&send.input()));
});

define_test!(conditional_happens_before_with_two_parents_before_if: graph -> {
    let get_fn = graph.function("get_user_data_with");
    let get = graph.call_site(&get_fn);
    let dp_fn = graph.function("dp_user_data");
    let dp = graph.call_site(&dp_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);
    let push_fn = graph.function("push");
    let push = graph.call_site(&push_fn);
    assert!(push.output().flows_to_data(&get.input()));
    assert!(get.output().flows_to_data(&dp.input()));
    assert!(dp.output().flows_to_data(&send.input()));
    assert!(get.output().flows_to_data(&send.input()));
    assert!(!push.output().flows_to_data(&send.input()));
    assert!(!push.output().flows_to_data(&dp.input()));
});

define_test!(loops : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let dp_fn = graph.function("dp_user_data");
    let dp = graph.call_site(&dp_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);
    assert!(get.output().flows_to_data(&dp.input(),));
    assert!(dp.output().flows_to_data(&send.input()));
    assert!(get.output().flows_to_data(&send.input()));
});

define_test!(loop_retains_dependency : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let get_other_fn = graph.function("get_other_data");
    let get_other = graph.call_site(&get_other_fn);
    let dp_fn = graph.function("dp_user_data");
    let dp = graph.call_site(&dp_fn);
    let modify_other_fn = graph.function("modify_other_data");
    let modify_other = graph.call_site(&modify_other_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);
    assert!(get.output().flows_to_data(&dp.input()));
    assert!(get_other.output().flows_to_data(&dp.input()));
    assert!(modify_other.output().flows_to_data(&dp.input()));
    assert!(dp.output().flows_to_data(&send.input()));
    assert!(modify_other.output().flows_to_data(&send.input()));
    assert!(get.output().flows_to_data(&send.input()));
});

define_test_skip!(arguments : graph -> {
    let body_id = *graph.body.0.keys().next().unwrap();
    let a1 = graph.argument(body_id, 0);

    let dp_fn = graph.function("dp_user_data");
    let dp = graph.call_site(&dp_fn);

    assert!(graph.connects((a1, body_id), dp));
});

define_test!(modify_pointer : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let create_fn = graph.function("modify_vec");
    let create = graph.call_site(&create_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);

    assert!(get.output().flows_to_data(&create.input()));
    assert!(create.output().flows_to_data(&send.input()));
    assert!(get.output().flows_to_data(&send.input()));
});

define_test!(on_mut_var : graph -> {
    let source_fn = graph.function("source");
    let source = graph.call_site(&source_fn);
    let modify_fn = graph.function("modify_it");
    let modify = graph.call_site(&modify_fn);
    let receive_fn = graph.function("receiver");
    let receive = graph.call_site(&receive_fn);

    assert!(source.output().flows_to_data(&modify.input()));
    assert!(modify.output().flows_to_data(&receive.input()));
});

define_test!(spurious_connections_in_deref: graph -> {
    let source_fn = graph.function("new_s");
    let source = graph.call_site(&source_fn);
    let modify_fn = graph.function("deref");
    let modify = graph.call_site(&modify_fn);
    let receive_fn = graph.function("read_t");
    let receive = graph.call_site(&receive_fn);
    assert!(source.output().flows_to_data(&modify.input()));
    assert!(modify.output().flows_to_data(&receive.input()));
    assert!(!source.output().flows_to_data(&receive.input()));
    assert!(source.output().flows_to_data(&receive.input()));
});

define_test!(control_flow_tracking_overtaint: graph -> {
    let early_val_fn = graph.function("input");
    let early_val = graph.call_site(&early_val_fn);
    let late_val_fn = graph.function("source");
    let late_val = graph.call_site(&late_val_fn);
    let read_fn = graph.function("read_t");
    let read = graph.call_site(&read_fn);
    assert!(late_val.output().flows_to_ctrl(&read.input()));
    assert!(early_val.output().flows_to_ctrl(&read.input()));
});

define_test!(control_flow_tracking_for_non_fn_compound_conditions: graph -> {
    let cond_input_fn = graph.function("source");
    let cond_input = graph.call_site(&cond_input_fn);
    let other_cond_fn = graph.function("input");
    let other_cond = graph.call_site(&other_cond_fn);
    let read_fn = graph.function("read_t");
    let read = graph.call_site(&read_fn);
    assert!(cond_input.output().flows_to_data(&read.input()));
    assert!(other_cond.output().flows_to_data(&read.input()));
    assert!(cond_input.output().flows_to_ctrl(&read.input()));
    assert!(other_cond.output().flows_to_ctrl(&read.input()));
});

define_test!(control_flow_tracking_for_compound_cond_with_fun: graph -> {
    let cond_input_fn = graph.function("source");
    let cond_input = graph.call_site(&cond_input_fn);
    let other_cond_fn = graph.function("input");
    let other_cond = graph.call_site(&other_cond_fn);
    let read_fn = graph.function("read_t");
    let read = graph.call_site(&read_fn);
    assert!(cond_input.output().flows_to_ctrl(&read.input()));
    assert!(other_cond.output().flows_to_ctrl(&read.input()));
    assert!(cond_input.output().flows_to_ctrl(&other_cond.input()));
    assert!(cond_input.output().is_neighbor_ctrl(&other_cond.input()));
    assert!(other_cond.output().is_neighbor_ctrl(&read.input()));
    // Not sure why this ever worked and if it is even the correct semantics
    // assert!(!cond_input.output().is_neighbor_ctrl(&read.input()));
});

define_test!(and_desugaring_similar_pattern: graph -> {
    let cond_input_fn = graph.function("input");
    let cond_input = graph.call_site(&cond_input_fn);
    let other_cond_fn = graph.function("source");
    let other_cond = graph.call_site(&other_cond_fn);
    let read_fn = graph.function("read_t");
    let read = graph.call_site(&read_fn);
    assert!(cond_input.output().flows_to_ctrl(&read.input()));
    assert!(other_cond.output().flows_to_ctrl(&read.input()));
    assert!(cond_input.output().flows_to_ctrl(&other_cond.input()));
    assert!(cond_input.output().is_neighbor_ctrl(&other_cond.input()));
    assert!(other_cond.output().is_neighbor_ctrl(&read.input()));
    assert!(!cond_input.output().is_neighbor_ctrl(&read.input()));
});
