#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

mod helpers;
use helpers::*;

fn do_in_crate_dir<A, F: std::panic::UnwindSafe + FnOnce() -> A>(f: F) -> std::io::Result<A> {
    let crate_dir: std::path::PathBuf = "tests/forge-tests".to_string().into();
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

#[test]
fn vacuity() {
    assert!(*TEST_CRATE_ANALYZED);

    assert!(create_forge_file("vacuity", "", "sat"));
    assert!(get_forge_result("vacuity"));
}

#[test]
fn control_flow() {
    assert!(*TEST_CRATE_ANALYZED);

    assert!(create_forge_file(
        "process_invalid_check",
        "check_always_happens[`process_invalid_check]",
        "theorem"
    ));
    assert!(!get_forge_result("process_invalid_check"));

    assert!(create_forge_file(
        "process_if",
        "check_always_happens[`process_if]",
        "theorem"
    ));
    assert!(get_forge_result("process_if"));
}

#[test]
fn blessing_safe_sources() {
    assert!(*TEST_CRATE_ANALYZED);

    assert!(create_forge_file(
        "blessed_safe_sources",
        "only_send_to_allowed_sources[`blessed_safe_sources]",
        "theorem"
    ));
    assert!(get_forge_result("blessed_safe_sources"));

    assert!(create_forge_file(
        "only_safe_sources",
        "only_send_to_allowed_sources[`only_safe_sources]",
        "theorem"
    ));
    assert!(get_forge_result("only_safe_sources"));

    assert!(create_forge_file(
        "unblessed_safe_sources_with_bless",
        "only_send_to_allowed_sources[`unblessed_safe_sources_with_bless]",
        "theorem"
    ));
    assert!(!get_forge_result("unblessed_safe_sources_with_bless"));

    assert!(create_forge_file(
        "unsafe_sources",
        "only_send_to_allowed_sources[`unsafe_sources]",
        "theorem"
    ));
    assert!(!get_forge_result("unsafe_sources"));

    assert!(create_forge_file(
        "blessed_and_unblessed_safe_sources",
        "only_send_to_allowed_sources[`blessed_and_unblessed_safe_sources]",
        "theorem"
    ));
    assert!(!get_forge_result("blessed_and_unblessed_safe_sources"));
}

#[test]
fn conditional_modification() {
    assert!(*TEST_CRATE_ANALYZED);

    assert!(create_forge_file(
        "conditional_modification",
        "only_send_to_allowed_sources[`conditional_modification]",
        "theorem"
    ));
    // TODO:(livia) Below fails, see forge-tests/main.rs
    // assert!(get_forge_result("conditional_modification"));
}
