#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use dfpp::Symbol;
mod helpers;
use helpers::*;

fn do_in_crate_dir<A, F: std::panic::UnwindSafe + FnOnce() -> A>(f: F) -> std::io::Result<A> {
    with_current_directory("tests/new-alias-analysis-tests", f)
}

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = *helpers::DFPP_INSTALLED
        && do_in_crate_dir(|| { run_dfpp_with_graph_dump() }).map_or_else(
            |e| {
                println!("io err {}", e);
                false
            },
            |t| t
        );
}

macro_rules! define_test {
    ($name:ident : $graph:ident -> $block:block) => {
        #[test]
        fn $name() {
            assert!(*TEST_CRATE_ANALYZED);
            use_rustc(|| {
                let $graph =
                    do_in_crate_dir(|| G::from_file(Symbol::intern(stringify!($name)))).unwrap();
                $block
            });
        }
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
