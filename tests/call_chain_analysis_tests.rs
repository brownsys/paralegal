#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

mod helpers;

use helpers::*;

const TEST_CRATE_NAME: &'static str = "tests/call-chain-analysis-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = {
        let crate_dir: std::path::PathBuf = TEST_CRATE_NAME.to_string().into();
        *DFPP_INSTALLED
            && cwd_and_use_rustc_in(&crate_dir, || run_dfpp_with_flow_graph_dump()).map_or_else(
                |e| {
                    println!("io err {}", e);
                    false
                },
                |t| t,
            )
    };
}

#[test]
fn simple() {
    assert!(*TEST_CRATE_ANALYZED);
    let graph = PreFrg::from_file_at(TEST_CRATE_NAME);
    use_rustc(|| {
        let src_fn = graph.function("source");
        let src = src_fn.call_sites().pop().unwrap();
        let dest_fn = graph.function("receiver");
        let dest_sink = dest_fn.call_sites().pop().unwrap();
        let dest = dest_sink.input().pop().unwrap();

        assert!(src.flows_to(&dest));
    })
}
