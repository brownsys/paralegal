#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

mod helpers;

use helpers::*;

const TEST_CRATE_NAME: &str = "tests/call-chain-analysis-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = {
        let crate_dir: std::path::PathBuf = TEST_CRATE_NAME.to_string().into();
        *DFPP_INSTALLED
            && cwd_and_use_rustc_in(&crate_dir, run_dfpp_with_flow_graph_dump).map_or_else(
                |e| {
                    println!("io err {}", e);
                    false
                },
                |t| t,
            )
    };
}

macro_rules! define_test {
    ($name:ident $graph:ident $block:block) => {
        #[test]
        fn $name() {
            assert!(*TEST_CRATE_ANALYZED);
            use_rustc(|| {
                let $graph = PreFrg::from_file_at(TEST_CRATE_NAME);
                $block
            })
        }
    };
}

define_test!(without_return graph {
    let src_fn = graph.function("source");
    let ctrl = graph.ctrl("without_return");
    let src = ctrl.call_site(&src_fn);
    let dest_fn = graph.function("receiver");
    let dest_sink = ctrl.call_site(&dest_fn);
    let dest = dest_sink.input().pop().unwrap();

    assert!(src.flows_to(&dest));
});

define_test!(with_return graph {
    let src_fn = graph.function("source");
    let ctrl = graph.ctrl("with_return");
    let src = ctrl.call_site(&src_fn);
    let dest_fn = graph.function("receiver");
    let dest_sink = ctrl.call_site(&dest_fn);
    let dest = dest_sink.input().pop().unwrap();

    assert!(src.flows_to(&dest));
});

define_test!(on_mut_var graph {
    let src_fn = graph.function("source");
    let ctrl = graph.ctrl("on_mut_var");
    let src = ctrl.call_site(&src_fn);
    let dest_fn = graph.function("receiver");
    let dest_sink = ctrl.call_site(&dest_fn);
    let dest = dest_sink.input().pop().unwrap();

    assert!(src.flows_to(&dest));
});

define_test!(on_mut_var_no_modify graph {
    let src_fn = graph.function("source");
    let ctrl = graph.ctrl("on_mut_var_no_modify");
    if let Some(src) = ctrl.call_sites(&src_fn).pop() {
        let dest_fn = graph.function("receiver");
        if let Some(dest_sink) = ctrl.call_sites(&dest_fn).pop() {
            if let Some(dest) = dest_sink.input().pop() {
                assert!(!src.flows_to(&dest));
            }
        }
    }
});

define_test!(field_sensitivity graph {
    let produce_usize_fn = graph.function("produce_usize");
    let produce_string_fn = graph.function("produce_string");
    let consume_usize_fn = graph.function("read_usize");
    let consume_string_fn = graph.function("read_string");
    let ctrl = graph.ctrl("field_sensitivity");
    let produce_usize = ctrl.call_site(&produce_usize_fn);
    let produce_string = ctrl.call_site(&produce_string_fn);
    let read_string = ctrl.call_site(&consume_string_fn);
    let read_usize = ctrl.call_site(&consume_usize_fn);
    assert!(produce_usize.flows_to(&read_usize.input()[0]));
    assert!(!produce_usize.flows_to(&read_string.input()[0]));
    assert!(produce_string.flows_to(&read_string.input()[0]));
});
