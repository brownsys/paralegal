#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use dfpp::Symbol;
mod helpers;
use helpers::*;

const CRATE_DIR: &str = "tests/inconsequential-call-removal-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = *helpers::DFPP_INSTALLED
        && with_current_directory(CRATE_DIR, || { run_dfpp_with_graph_dump_and(["--remove-inconsequential-calls", "conservative"]) }).map_or_else(
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

define_test!(single_removal: graph -> {
    let create = graph.function_call("create");
    let read = graph.function_call("read");
    let push = graph.function_call("push");

    assert!(graph.connects_none(&push));
    assert!(graph.connects_direct(&create, &read));
});

define_test!(double_removal: graph -> {

    let create = graph.function_call("create");
    let read = graph.function_call("read");
    let push = graph.function_call("push");
    let truncate = graph.function_call("truncate");

    assert!(graph.connects_none(&push));
    assert!(graph.connects_none(&truncate));
    assert!(graph.connects_direct(&create, &read));
});

define_test!(labeled_function_not_removed: graph -> {
    let create = graph.function_call("create");
    let read = graph.function_call("read");
    let push = graph.function_call("other_push");

    assert!(graph.connects(&create, &push));
    assert!(graph.connects(&push, &read));
});

define_test!(source_function_not_removed: graph -> {
    let create = graph.function_call("new");
    let read = graph.function_call("read");
    let push = graph.function_call("push");

    assert!(graph.connects_none(&push));
    assert!(graph.connects_direct(&create, &read));
});

define_test!(sink_function_not_removed: graph -> {
    let create = graph.function_call("create_string");
    let write = graph.function_call("write");
    let as_bytes = graph.function_call("as_bytes");

    assert!(graph.connects_none(&as_bytes));
    assert!(graph.connects(&create, &write))
});

define_test!(no_removal_because_ctrl_out: graph -> {
    let create = graph.function_call("create");
    let read = graph.function_call("read");
    let is_empty = graph.function_call("is_empty");

    assert!(graph.connects(&create, &read));
    assert!(graph.connects_data(&create, &is_empty));
    assert!(graph.connects_ctrl(&is_empty, &read));
});

define_test!(removal_despite_ctrl_in: graph -> {
    let create = graph.function_call("create");
    let read = graph.function_call("read");
    let push = graph.function_call("push");

    assert!(graph.connects_none(&push));
    assert!(graph.connects_direct(&create, &read));
});

define_test!(cross_connection_after_removal: graph -> {
    let create = graph.function_call("create(");
    let read = graph.function_call("read(");
    let create2 = graph.function_call("create2");
    let read2 = graph.function_call("read2");
    let swap = graph.function_call("swap_with_slice");

    assert!(graph.connects_none(&swap));
    assert!(graph.connects_direct(&create, &read));
    assert!(graph.connects_direct(&create2, &read2));
    assert!(graph.connects_direct(&create2, &read));
    assert!(graph.connects_direct(&create, &read2));

});