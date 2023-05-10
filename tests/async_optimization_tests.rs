#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use dfpp::Symbol;
mod helpers;
use helpers::*;

const CRATE_DIR: &str = "tests/async-optimization-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = *helpers::DFPP_INSTALLED
        && with_current_directory(CRATE_DIR, || {
            run_dfpp_with_graph_dump_and(&["--drop-poll"])
        })
        .map_or_else(
            |e| {
                println!("io err {}", e);
                false
            },
            |t| t
        );
}

macro_rules! define_test {
    ($name:ident :  $graph:ident -> $block:block) => {
        define_G_test_template!(TEST_CRATE_ANALYZED, CRATE_DIR, $name : $graph -> $block);
    };
}

define_test!(remove_poll_match: graph -> {
    let input = graph.function_call("some_input");
    let target = graph.function_call("target");
    let poll = graph.function_call("poll");
    let new_unchecked = graph.function_call("new_unchecked");
    let get_context = graph.function_call("get_context");
    let into_future = graph.function_call("into_future");
    let f = graph.function_call(" f(");
    assert!(graph.connects_data(&input, &target));

    assert!(graph.connects_none(&poll));
    assert!(graph.connects_none(&new_unchecked));
    assert!(graph.connects_none(&get_context));
    assert!(graph.connects_none(&into_future));
});
