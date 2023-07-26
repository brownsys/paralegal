#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

mod helpers;
use helpers::*;

fn do_in_crate_dir<A, F: std::panic::UnwindSafe + FnOnce() -> A>(f: F) -> std::io::Result<A> {
    with_current_directory(CRATE_DIR, f)
}

const CRATE_DIR: &str = "tests/external-annotation-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_dfpp_with_graph_dump_and(
        CRATE_DIR,
        ["--external-annotations", "external-annotations.toml"]
    );
}
// This will create a forge file with the name "test_{test_name}.frg"
// that test expects that running {property} for Flows is {result}.
// To test a predicate on a specific ctrl, property should be of the form
// pred[`ctrl_name]
fn create_forge_file(test_name: &str, property: &str, result: &str) -> bool {
    do_in_crate_dir(|| write_forge(&format!("test_{}.frg", test_name), property, result))
        .map_or_else(
            |e| {
                println!("io err {}", e);
                false
            },
            |_| true,
        )
}

// This will return true if running the file passes all of the tests,
// and false otherwise.
fn get_forge_result(test_name: &str) -> bool {
    do_in_crate_dir(|| run_forge(&format!("test_{}.frg", test_name))).map_or_else(
        |e| {
            println!("io err {}", e);
            false
        },
        |t| t,
    )
}

fn create_and_run(test_name: &str, property: &str, result: &str) -> bool {
    assert!(create_forge_file(test_name, property, result));
    get_forge_result(test_name)
}

#[test]
fn type_marker() {
    assert!(*TEST_CRATE_ANALYZED);
    assert!(create_and_run(
        "type_marker",
        "some labels.type_marker & Type",
        "sat"
    ));
}

#[test]
fn function_marker() {
    assert!(*TEST_CRATE_ANALYZED);
    assert!(create_and_run(
        "function_marker",
        "some labels.function_marker & Function",
        "sat"
    ));
}

#[test]
fn argument_marker() {
    assert!(*TEST_CRATE_ANALYZED);
    assert!(create_and_run(
        "argument_marker",
        "some labels.argument_marker & CallArgument",
        "sat"
    ));
}

#[test]
fn return_marker() {
    assert!(*TEST_CRATE_ANALYZED);
    assert!(create_and_run(
        "return_marker",
        "some labels.return_marker & CallSite",
        "sat"
    ));
}
