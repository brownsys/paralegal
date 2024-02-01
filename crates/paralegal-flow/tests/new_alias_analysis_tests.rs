#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use paralegal_flow::{define_flow_test_template, test_utils::*, Symbol};

const CRATE_DIR: &str = "tests/new-alias-analysis-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump(CRATE_DIR);
}

macro_rules! define_test {
    ($name:ident: $ctrl:ident -> $block:block) => {
        define_test!($name: $ctrl, $name -> $block);
    };
    ($name:ident: $ctrl:ident, $ctrl_name:ident -> $block:block) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, CRATE_DIR, $name: $ctrl, $ctrl_name -> $block);
    };
}

define_test!(track_mutable_modify : graph -> {
    let source_fn = graph.function("new_s");
    let source = graph.call_site(&source_fn);
    let modify_fn = graph.function("modify_it");
    let modify = graph.call_site(&modify_fn);
    let read_fn = graph.function("read");
    let read = graph.call_site(&read_fn);

    assert!(source.output().is_neighbor_data(&modify.input()));
    assert!(modify.output().is_neighbor_data(&read.input()));
    assert!(source.output().is_neighbor_data(&read.input()));
});

define_test!(eliminate_return_connection : graph -> {
    let source_fn = graph.function("new_s");
    let source = graph.call_site(&source_fn);
    let pass_through_fn = graph.function("deref_t");
    let pass_through = graph.call_site(&pass_through_fn);
    let read_fn = graph.function("read");
    let read = graph.call_site(&read_fn);

    assert!(source.output().is_neighbor_data(&pass_through.input()));
    assert!(pass_through.output().is_neighbor_data(&read.input()));
    assert!(!source.output().is_neighbor_data(&read.input()));
});

define_test!(eliminate_mut_input_connection : graph -> {
    let source_fn = graph.function("new_s");
    let source = graph.call_site(&source_fn);
    let push_fn = graph.function("push");
    let push = graph.call_site(&push_fn);
    let read_fn = graph.function("read");
    let read = graph.call_site(&read_fn);

    assert!(source.output().is_neighbor_data(&push.input()));
    assert!(push.output().is_neighbor_data(&read.input()));
    assert!(!source.output().is_neighbor_data(&read.input()));
});

define_test!(input_elimination_isnt_a_problem_empty : graph -> {
    let source_fn = graph.function("new_s");
    let source = graph.call_site(&source_fn);
    let read_fn = graph.function("read");
    let read = graph.call_site(&read_fn);

    assert!(!source.output().flows_to_data(&read.input()));
});

define_test!(input_elimination_isnt_a_problem_vec_push : graph -> {
    let source_fn = graph.function("new_s");
    let source = graph.call_site(&source_fn);
    let push_fn = graph.function("push");
    let push = graph.call_site(&push_fn);
    let insert_fn = graph.function("insert(");
    let insert = graph.call_site(&insert_fn);
    let read_fn = graph.function("read");
    let read = graph.call_site(&read_fn);

    assert!(source.output().is_neighbor_data(&insert.input()));
    assert!(insert.output().is_neighbor_data(&push.input()));
    assert!(push.output().is_neighbor_data(&read.input()));
    assert!(source.output().is_neighbor_data(&push.input()));
    assert!(!insert.output().is_neighbor_data(&read.input()));
    assert!(!source.output().is_neighbor_data(&read.input()));
});

define_test!(input_elimination_isnt_a_problem_statement : graph -> {
    let src_1_fn = graph.function("new_s");
    let src_1 = graph.call_site(&src_1_fn);
    let src_2_fn = graph.function("another_s");
    let src_2 = graph.call_site(&src_2_fn);

    let assoc_fn = graph.function("assoc");
    let assoc = graph.call_site(&assoc_fn);

    let read_fn = graph.function("read");
    let read = graph.call_site(&read_fn);

    assert!(src_1.output().is_neighbor_data(&assoc.input()));
    assert!(assoc.output().is_neighbor_data(&read.input()));
    assert!(src_2.output().is_neighbor_data(&read.input()));
    assert!(!src_1.output().is_neighbor_data(&read.input()));
});

define_test!(no_inlining_overtaint : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let get2_fn = graph.function("get2_user_data");
    let get2 = graph.call_site(&get2_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);
    let send2_fn = graph.function("send2_user_data");
    let send2 = graph.call_site(&send2_fn);
    let dp_fn = graph.function("dp1_user_data");
    let dp = graph.call_site(&dp_fn);

    assert!(get.output().flows_to_data(&send.input()));
    assert!(get2.output().flows_to_data(&send2.input()));
    assert!(get2.output().flows_to_data(&dp.input()));
    assert!(!get.output().flows_to_data(&dp.input()));

    assert!(!get.output().flows_to_data(&send2.input()));
    assert!(!get2.output().flows_to_data(&send.input()));
});
