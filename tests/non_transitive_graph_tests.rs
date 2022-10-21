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
    static ref TEST_CRATE_ANALYZED: bool = install_dfpp()
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

    assert!(graph.connects(get, dp));
    assert!(graph.connects(dp, send));
    assert!(graph.connects(get, send));
    assert!(!graph.connects_direct(get, send))
}

#[test]
fn happens_before_if_has_connections() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph =
        do_in_crate_dir(|| G::from_file(Symbol::intern("conditional_happens_before"))).unwrap();

    let get = graph.function_call("get_user_data");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");
    assert!(graph.connects(get, dp,));
    assert!(graph.connects(dp, send));
    assert!(graph.connects_direct(get, send));
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
    assert!(graph.connects(get, dp,));
    assert!(graph.connects(dp, send));
    assert!(graph.connects_direct(get, send));
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
    assert!(graph.connects(push, get));
    assert!(graph.connects(get, dp));
    assert!(graph.connects(dp, send));
    assert!(graph.connects_direct(get, send));
    assert!(!graph.connects_direct(push, send));
    assert!(!graph.connects_direct(push, dp));
}

#[test]
fn loops() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("loops"))).unwrap();

    let get = graph.function_call("get_user_data");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");
    assert!(graph.connects(get, dp,));
    assert!(graph.connects(dp, send));
    assert!(graph.connects_direct(get, send));
}

#[allow(dead_code)]
fn arguments() {
    assert!(*TEST_CRATE_ANALYZED);

    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("args"))).unwrap();

    let a1 = graph.argument(0);

    let dp = graph.function_call("dp_user_data");

    assert!(graph.connects(a1, dp));
}
