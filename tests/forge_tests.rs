#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use dfpp::Symbol;
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

fn get_forge_result(file: &str) -> bool {
	do_in_crate_dir(|| { run_forge(file) }).map_or_else(
		|e| {
			println!("io err {}", e);
			false
		},
		|t| t
	)
}

#[test]
fn t() {
    assert!(*TEST_CRATE_ANALYZED);
	
	assert!(get_forge_result("forge/allowed_sources.frg"));
}