#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use dfpp::Symbol;
mod helpers;
use helpers::*;

const CRATE_DIR: &str = "tests/new-alias-analysis-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = *helpers::DFPP_INSTALLED
        && with_current_directory(CRATE_DIR, || { run_dfpp_with_graph_dump() }).map_or_else(
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

define_test!(track_mutable_modify : graph -> {
    let source = &graph.function_call("new_s");
    let modify = &graph.function_call("modify_it");
    let read = &graph.function_call("read");

    assert!(graph.connects_direct(source, modify));
    assert!(graph.connects_direct(modify, read));
    assert!(graph.connects_direct(source, read));
});

define_test!(eliminate_return_connection : graph -> {
    let source = &graph.function_call("new_s");
    let pass_through = &graph.function_call("deref_t");
    let read = &graph.function_call("read");

    assert!(graph.connects_direct(source, pass_through));
    assert!(graph.connects_direct(pass_through, read));
    assert!(!graph.connects_direct(source, read));
});

define_test!(eliminate_mut_input_connection : graph -> {
    let source = &graph.function_call("new_s");
    let push = &graph.function_call("push");
    let read = &graph.function_call("read");

    assert!(graph.connects_direct(source, push));
    assert!(graph.connects_direct(push, read));
    assert!(!graph.connects_direct(source, read));
});

define_test!(input_elimination_isnt_a_problem_empty : graph -> {
    let source = &graph.function_call("new_s");
    let read = &graph.function_call("read");

    assert!(!graph.connects(source, read));
});

define_test!(input_elimination_isnt_a_problem_vec_push : graph -> {
    let source = &graph.function_call("new_s");
    let push = &graph.function_call("push");
    let insert = &graph.function_call("insert(");
    let read = &graph.function_call("read");

    assert!(graph.connects_direct(source, insert));
    assert!(graph.connects_direct(insert, push));
    assert!(graph.connects_direct(push, read));
    assert!(graph.connects_direct(source, push));
    assert!(!graph.connects_direct(insert, read));
    assert!(!graph.connects_direct(source, read));
});

define_test!(input_elimination_isnt_a_problem_statement : graph -> {
    let src_1 = &graph.function_call("new_s");
    let src_2 = &graph.function_call("another_s");

    let assoc = &graph.function_call("assoc");

    let read = &graph.function_call("read");

    assert!(graph.connects_direct(src_1, assoc));
    assert!(graph.connects_direct(assoc, read));
    assert!(graph.connects_direct(src_2, read));
    assert!(!graph.connects_direct(src_1, read));
});

define_test!(no_inlining_overtaint : graph -> {
    let get = graph.function_call(" get_user_data(");
    let get2 = graph.function_call("get_user_data2");
    let send = graph.function_call("send_user_data(");
    let send2 = graph.function_call("send_user_data2");
    let dp = graph.function_call(" dp_user_data");

    assert!(graph.connects(&get, &send));
    assert!(graph.connects(&get2, &send2));
    assert!(graph.connects_data(&get2, &dp));
    assert!(!graph.connects_data(&get, &dp));

    assert!(!graph.connects(&get, &send2));
    assert!(!graph.connects(&get2, &send));
});
