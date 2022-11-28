#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use dfpp::Symbol;
mod helpers;
use helpers::*;

fn do_in_crate_dir<A, F: std::panic::UnwindSafe + FnOnce() -> A>(f: F) -> std::io::Result<A> {
    let crate_dir: std::path::PathBuf = "tests/control-flow-tests".to_string().into();
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
fn process_basic() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("process_basic"))).unwrap();

    let get = graph.function_call("get_user_data");
    let check = graph.function_call("check_user_data");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &check));
    assert!(!graph.connects(&check, &send));
    assert!(graph.connects(&get, &send));
    assert!(graph.connects_direct(&get, &send));
}

#[test]
fn process_if() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("process_if"))).unwrap();

    let get = graph.function_call("get_user_data");
    let check = graph.function_call("check_user_data");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &check));
    assert!(graph.connects(&check, &send));
    assert!(graph.connects(&get, &send));
    assert!(graph.connects_direct(&get, &send));
    assert!(graph.connects_direct(&check, &send));
}

#[test]
fn process_if_after() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("process_if_after"))).unwrap();

    let get = graph.function_call("get_user_data");
    let check = graph.function_call("check_user_data");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &check));
    assert!(graph.connects(&check, &send));
    assert!(graph.connects(&get, &send));
    assert!(graph.connects_direct(&get, &send));
    assert!(!graph.connects_direct(&check, &send));
}

#[test]
fn process_nested_if() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("process_nested_if"))).unwrap();

    let get = graph.function_call("get_user_data");
    let check = graph.function_call("check_user_data");
	let check2 = graph.function_call("check2");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &check));
    assert!(graph.connects(&check, &send));
	assert!(graph.connects(&check2, &send));
    assert!(graph.connects(&get, &send));
    assert!(graph.connects_direct(&get, &send));
    assert!(graph.connects_direct(&check, &check2));
	assert!(graph.connects_direct(&check2, &send));
}

#[test]
fn process_if_multiple_statements() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("process_if_multiple_statements"))).unwrap();

    let get = graph.function_call("get_user_data");
    let check = graph.function_call("check_user_data");
	let modify = graph.function_call("modify");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &check));
    assert!(graph.connects(&check, &modify));
	assert!(graph.connects(&check, &send));
    assert!(graph.connects(&get, &send));
    assert!(!graph.connects_direct(&get, &send));
    assert!(graph.connects_direct(&check, &modify));
	assert!(graph.connects_direct(&check, &send));
	assert!(graph.connects_direct(&modify, &send));
}

#[test]
fn process_if_not_function_call() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("process_if_not_function_call"))).unwrap();

	let getx = graph.function_call("get_x");
    let get = graph.function_call("get_user_data");
	let modify = graph.function_call("modify");
    let send = graph.function_call("send_user_data");

    assert!(!graph.connects(&getx, &get));
    assert!(graph.connects_direct(&get, &send));
	assert!(graph.connects_direct(&getx, &modify));
	assert!(graph.connects(&getx, &send));
    assert!(!graph.connects_direct(&getx, &send));
}

#[test]
fn process_no_args() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = do_in_crate_dir(|| G::from_file(Symbol::intern("process_no_args"))).unwrap();

	let getx = graph.function_call("get_x");
    let get = graph.function_call("get_user_data");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&getx, &get)); // TODO: This passes but doesn't show up in frg.
    assert!(graph.connects(&get, &send));
	assert!(graph.connects(&getx, &send));
    assert!(graph.connects_direct(&get, &send));
    assert!(graph.connects_direct(&getx, &get));
}
