#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use dfpp::Symbol;
mod helpers;
use helpers::*;

const CRATE_DIR: &str = "tests/inline-no-arg-closure-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = *helpers::DFPP_INSTALLED
        && with_current_directory(CRATE_DIR, || {
            run_dfpp_with_graph_dump_and(["--inline-no-arg-closures"])
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

define_test!(simple: graph -> {
    let src = graph.function_call("input");
    let sink = graph.function_call("sink");
    assert!(graph.connects(&src, &sink));
});

define_test!(local: graph -> {
    let src = graph.function_call("input");
    let sink = graph.function_call("sink");
    assert!(graph.connects(&src, &sink));
});

define_test!(closure_arg: graph -> {
    let src = graph.function_call("input");
    let sink = graph.function_calls("sink").into_iter().collect::<Vec<_>>();
    assert!(sink.is_empty() || (sink.len() == 1 && !graph.connects(&src, &sink[0])))
});

define_test!(caller_arg: graph -> {
    let src = graph.function_call("input");
    let sink = graph.function_calls("sink").into_iter().collect::<Vec<_>>();
    assert!(sink.is_empty() || (sink.len() == 1 && !graph.connects(&src, &sink[0])))
});
define_test!(return_connect: graph -> {
    let src = graph.function_call("input");
    let sink = graph.function_call("sink");
    assert!(graph.connects(&src, &sink));
});
