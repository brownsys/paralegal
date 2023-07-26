#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

mod helpers;
use helpers::*;
use serial_test::serial;

const TEST_CRATE_NAME: &str = "tests/forge-tests";

fn do_in_crate_dir<A, F: std::panic::UnwindSafe + FnOnce() -> A>(f: F) -> std::io::Result<A> {
    with_current_directory(TEST_CRATE_NAME, f)
}

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = {
        let crate_dir: std::path::PathBuf = TEST_CRATE_NAME.to_string().into();
        cwd_and_use_rustc_in(crate_dir, run_dfpp_with_flow_graph_dump).map_or_else(
            |e| {
                println!("io err {}", e);
                false
            },
            |t| t,
        )
    };
}

// This will create a forge file with the name "test_{test_name}.frg"
// that test expects that running {property[`ctrl]} for Flows is {result}.
// To test a predicate on a specific ctrl, property should be of the form
// pred[`ctrl_name]
fn create_forge_file(test_name: &str, property: &str, ctrl: Option<&str>, result: &str) -> bool {
    use_rustc(|| {
        let property = match ctrl {
            Some(c) => {
                let graph = PreFrg::from_file_at(TEST_CRATE_NAME);
                let ctrl_hashed = graph.ctrl_hashed(c);
                format!("{}[`{}]", property, ctrl_hashed.as_str())
            }
            None => property.to_owned(),
        };

        do_in_crate_dir(|| write_forge(&format!("test_{}.frg", test_name), &property, result))
            .map_or_else(
                |e| {
                    println!("io err {}", e);
                    false
                },
                |_| true,
            )
    })
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
#[serial]
fn vacuity() {
    assert!(*TEST_CRATE_ANALYZED);

    assert!(create_forge_file("vacuity", "", None, "sat"));
    assert!(get_forge_result("vacuity"));
}

#[test]
#[serial]
fn control_flow() {
    assert!(*TEST_CRATE_ANALYZED);

    assert!(create_forge_file(
        "process_invalid_check",
        "check_always_happens",
        Some("process_invalid_check"),
        "theorem"
    ));
    assert!(!get_forge_result("process_invalid_check"));

    assert!(create_forge_file(
        "process_if",
        "check_always_happens",
        Some("process_if"),
        "theorem"
    ));
    assert!(get_forge_result("process_if"));
}

#[test]
#[serial]
fn blessing_safe_sources() {
    assert!(*TEST_CRATE_ANALYZED);

    assert!(create_forge_file(
        "blessed_safe_sources",
        "only_send_to_allowed_sources",
        Some("blessed_safe_sources"),
        "theorem"
    ));
    assert!(get_forge_result("blessed_safe_sources"));

    assert!(create_forge_file(
        "only_safe_sources",
        "only_send_to_allowed_sources",
        Some("only_safe_sources"),
        "theorem"
    ));
    assert!(get_forge_result("only_safe_sources"));

    assert!(create_forge_file(
        "unblessed_safe_sources_with_bless",
        "only_send_to_allowed_sources",
        Some("unblessed_safe_sources_with_bless"),
        "theorem"
    ));
    assert!(!get_forge_result("unblessed_safe_sources_with_bless"));

    assert!(create_forge_file(
        "unsafe_sources",
        "only_send_to_allowed_sources",
        Some("unsafe_sources"),
        "theorem"
    ));
    assert!(!get_forge_result("unsafe_sources"));

    assert!(create_forge_file(
        "blessed_and_unblessed_safe_sources",
        "only_send_to_allowed_sources",
        Some("blessed_and_unblessed_safe_sources"),
        "theorem"
    ));
    assert!(!get_forge_result("blessed_and_unblessed_safe_sources"));
}

#[test]
#[serial]
fn conditional_modification() {
    assert!(*TEST_CRATE_ANALYZED);

    assert!(create_forge_file(
        "conditional_modification",
        "only_send_to_allowed_sources",
        Some("conditional_modification"),
        "theorem"
    ));
    // TODO:(livia) Below fails, see forge-tests/main.rs
    // assert!(get_forge_result("conditional_modification"));
}
