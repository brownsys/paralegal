#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use dfpp::Symbol;
mod helpers;
use helpers::*;

fn do_in_crate_dir<A, F: std::panic::UnwindSafe + FnOnce() -> A>(f: F) -> std::io::Result<A> {
    let crate_dir: std::path::PathBuf = "tests/new-alias-analysis-tests".to_string().into();
    cwd_and_use_rustc_in(&crate_dir, f)
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

#[test]
fn track_mutable_modify() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("track_mutable_modify"))).unwrap();

    let ref source = graph.function_call("new_s");
    let ref modify = graph.function_call("modify_it");
    let ref read = graph.function_call("read");

    assert!(graph.connects_direct(source, modify));
    assert!(graph.connects_direct(modify, read));
    assert!(graph.connects_direct(source, read));
}

#[test]
fn eliminate_return_connection() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph =
        do_in_crate_dir(|| G::from_file(Symbol::intern("eliminate_return_connection"))).unwrap();
    let ref source = graph.function_call("new_s");
    let ref pass_through = graph.function_call("deref_t");
    let ref read = graph.function_call("read");

    assert!(graph.connects_direct(source, pass_through));
    assert!(graph.connects_direct(pass_through, read));
    assert!(!graph.connects_direct(source, read));
}

#[test]
fn eliminate_mut_input_connection() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph =
        do_in_crate_dir(|| G::from_file(Symbol::intern("eliminate_mut_input_connection"))).unwrap();
    let ref source = graph.function_call("new_s");
    let ref push = graph.function_call("push");
    let ref read = graph.function_call("read");

    assert!(graph.connects_direct(source, push));
    assert!(graph.connects_direct(push, read));
    assert!(!graph.connects_direct(source, read));
}

#[test]
fn input_elimination_isnt_a_problem_empty() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph =
        do_in_crate_dir(|| G::from_file(Symbol::intern("input_elimination_isnt_a_problem_empty")))
            .unwrap();
    let ref source = graph.function_call("new_s");
    let ref read = graph.function_call("read");

    assert!(!graph.connects(source, read));
}

#[test]
fn input_elimination_isnt_a_problem_vec_push() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| {
        G::from_file(Symbol::intern("input_elimination_isnt_a_problem_vec_push"))
    })
    .unwrap();
    let ref source = graph.function_call("new_s");
    let ref push = graph.function_call("push");
    let ref insert = graph.function_call("insert(");
    let ref read = graph.function_call("read");

    assert!(graph.connects_direct(source, insert));
    assert!(graph.connects_direct(insert, push));
    assert!(graph.connects_direct(push, read));
    assert!(graph.connects_direct(source, push));
    assert!(!graph.connects_direct(insert, read));
    assert!(!graph.connects_direct(source, read));
}

#[test]
fn input_elimination_isnt_a_problem_statement() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| {
        G::from_file(Symbol::intern("input_elimination_isnt_a_problem_statement"))
    })
    .unwrap();

    let ref src_1 = graph.function_call("new_s");
    let ref src_2 = graph.function_call("another_s");

    let ref assoc = graph.function_call("assoc");

    let ref read = graph.function_call("read");

    assert!(graph.connects_direct(src_1, assoc));
    assert!(graph.connects_direct(assoc, read));
    assert!(graph.connects_direct(src_2, read));
    assert!(!graph.connects_direct(src_1, read));
}
