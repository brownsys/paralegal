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

fn create_forge_file(test_name: &str, property: &str, result: &str) -> bool {
	do_in_crate_dir(|| { write_forge(&format!("test_{}.frg", test_name), property, result) }).map_or_else(
		|e| {
			println!("io err {}", e);
			false
		},
		|_| true
	)
}

fn get_forge_result(test_name: &str) -> bool {
	do_in_crate_dir(|| { run_forge(&format!("test_{}.frg", test_name)) }).map_or_else(
		|e| {
			println!("io err {}", e);
			false
		},
		|t| t
	)
}

#[test]
fn vacuity() {
    assert!(*TEST_CRATE_ANALYZED);

	assert!(create_forge_file(
		"vacuity", 
		"", 
		"sat"));
	assert!(get_forge_result("vacuity"));
}

#[test]
fn control_flow() {
    assert!(*TEST_CRATE_ANALYZED);

	assert!(create_forge_file(
		"process_invalid_check", 
		"check_always_happens[`process_invalid_check]", 
		"theorem"));
	assert!(!get_forge_result("process_if"));
	
	assert!(create_forge_file(
		"process_if", 
		"check_always_happens[`process_if]", 
		"theorem"));
	assert!(get_forge_result("process_if"));
}