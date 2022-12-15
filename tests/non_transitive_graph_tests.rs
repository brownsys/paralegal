#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use dfpp::Symbol;
mod helpers;
use helpers::*;

fn do_in_crate_dir<A, F: std::panic::UnwindSafe + FnOnce() -> A>(f: F) -> std::io::Result<A> {
    let crate_dir: std::path::PathBuf = "tests/non-transitive-graph-tests".to_string().into();
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
fn simple_happens_before_has_connections() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("basic_happens_before"))).unwrap();

    let get = graph.function_call("get_user_data");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &dp));
    assert!(graph.connects(&dp, &send));
    assert!(graph.connects(&get, &send));
    assert!(!graph.connects_direct(&get, &send))
}

#[test]
fn happens_before_if_has_connections() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph =
        do_in_crate_dir(|| G::from_file(Symbol::intern("conditional_happens_before"))).unwrap();

    let get = graph.function_call("get_user_data");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");
    assert!(graph.connects(&get, &dp,));
    assert!(graph.connects(&dp, &send));
    assert!(graph.connects_direct(&get, &send));
}

#[test]
fn data_influenced_conditional_happens_before() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| {
        G::from_file(Symbol::intern("data_influenced_conditional_happens_before"))
    })
    .unwrap();

    let get = graph.function_call("get_user_data");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");
    assert!(graph.connects(&get, &dp,));
    assert!(graph.connects(&dp, &send));
    assert!(graph.connects_direct(&get, &send));
}

#[test]
fn conditional_happens_before_with_two_parents_before_if() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| {
        G::from_file(Symbol::intern(
            "conditional_happens_before_with_two_parents_before_if",
        ))
    })
    .unwrap();

    let get = graph.function_call("get_user_data_with");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");
    let push = graph.function_call("push");
    assert!(graph.connects(&push, &get));
    assert!(graph.connects(&get, &dp));
    assert!(graph.connects(&dp, &send));
    assert!(graph.connects_direct(&get, &send));
    assert!(!graph.connects_direct(&push, &send));
    assert!(!graph.connects_direct(&push, &dp));
}

#[test]
fn loops() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("loops"))).unwrap();

    let get = graph.function_call("get_user_data");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");
    assert!(graph.connects(&get, &dp,));
    assert!(graph.connects(&dp, &send));
    assert!(graph.connects_direct(&get, &send));
}

#[test]
fn loop_retains_dependency() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| {
        G::from_file(Symbol::intern("loop_retains_dependency"))
    })
    .unwrap();

    let get = graph.function_call("get_user_data");
    let get_other = graph.function_call("get_other_data");
    let dp = graph.function_call("dp_user_data");
    let modify_other = graph.function_call("modify_other_data");
    let send = graph.function_call("send_user_data");
    assert!(graph.connects(&get, &dp));
    assert!(graph.connects(&get_other, &dp));
    assert!(graph.connects(&modify_other, &dp));
    assert!(graph.connects(&dp, &send));
    assert!(graph.connects(&modify_other, &send));
    assert!(graph.connects_direct(&get, &send));
}

#[allow(dead_code)]
fn arguments() {
    assert!(*TEST_CRATE_ANALYZED);

    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("args"))).unwrap();
    let body_id = *graph.body.0.keys().next().unwrap();
    let a1 = graph.argument(body_id, 0);

    let dp = graph.function_call("dp_user_data");

    assert!(graph.connects(&(a1, body_id), &dp));
}

#[test]
fn modify_pointer() {
    assert!(*TEST_CRATE_ANALYZED);

    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("modify_pointer"))).unwrap();

    let get = graph.function_call("get_user_data");
    let create = graph.function_call("modify_vec");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &create));
    assert!(graph.connects(&create, &send));
    assert!(graph.connects(&get, &send));
}

#[test]
fn on_mut_var() {
    assert!(*TEST_CRATE_ANALYZED);

    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("on_mut_var"))).unwrap();

    let source = graph.function_call("source");
    let modify = graph.function_call("modify_it");
    let receive = graph.function_call("receiver");

    assert!(graph.connects(&source, &modify));
    assert!(graph.connects(&modify, &receive));
}

#[test]
fn spurious_connections_in_deref() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph =
        do_in_crate_dir(|| G::from_file(Symbol::intern("spurious_connections_in_derefs"))).unwrap();

    let ref source = graph.function_call("new_s");
    let ref modify = graph.function_call("deref");
    let ref receive = graph.function_call("read_t");
    assert!(graph.connects_direct(source, modify));
    assert!(graph.connects_direct(modify, receive));
    assert!(!graph.connects_direct(source, receive));
    assert!(graph.connects(source, receive));
}
