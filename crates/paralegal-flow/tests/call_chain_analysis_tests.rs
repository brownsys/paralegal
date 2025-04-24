#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

extern crate rustc_span;

use flowistry_pdg::GlobalLocation;
use paralegal_flow::{define_flow_test_template, test_utils::*};
use paralegal_spdg::utils::display_list;
use rustc_span::Symbol;

const TEST_CRATE_NAME: &str = "tests/call-chain-analysis-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump_and(
        TEST_CRATE_NAME,
        ["--local-crate-only", "--no-adaptive-approximation"]
    );
}

macro_rules! define_test {
    ($($t:tt)*) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, TEST_CRATE_NAME, $($t)*);
    };
}

define_test!(without_return: ctrl -> {
    let graph = ctrl.graph();
    let src_fn = graph.function("source");
    let src = ctrl.call_site(&src_fn);
    let dest_fn = graph.function("receiver");
    let dest_sink = ctrl.call_site(&dest_fn);
    let dest = dest_sink.input().nth(0).unwrap();

    assert!(src.output().flows_to_data(&dest));
});

#[test]
fn with_return() {
    InlineTestBuilder::new(stringify!(
        #[paralegal_flow::marker(hello, return)]
        fn source() -> i32 {
            0
        }
        fn callee(x: i32) -> i32 {
            source()
        }
        #[paralegal_flow::marker(there, arguments = [0])]
        fn receiver(x: i32) {}

        fn main(x: i32) {
            receiver(callee(x));
        }
    ))
    .with_extra_args(["--dump".to_string(), "spdg".to_string()])
    .check_ctrl(|ctrl| {
        let src_fn = ctrl.function("source");
        let src = ctrl.call_site(&src_fn);
        let dest_fn = ctrl.function("receiver");
        let dest_sink = ctrl.call_site(&dest_fn);
        let dest = dest_sink.input().nth(0).unwrap();

        assert!(!src.output().is_empty());
        assert!(!dest_sink.input().is_empty());

        assert!(src.output().flows_to_data(&dest));
    })
}

define_test!(on_mut_var: ctrl -> {
    let src_fn = ctrl.function("source");
    let src = ctrl.call_site(&src_fn);
    let dest_fn = ctrl.function("receiver");
    let dest_sink = ctrl.call_site(&dest_fn);
    let dest = dest_sink.input().nth(0).unwrap();

    assert!(src.output().flows_to_data(&dest));
});

define_test!(on_mut_var_no_modify: ctrl -> {
    let src_fn = ctrl.function("source");
    if let Some(src) = ctrl.call_sites(&src_fn).pop() {
        let dest_fn = ctrl.function("receiver");
        if let Some(dest_sink) = ctrl.call_sites(&dest_fn).pop() {
            assert!(!src.output().flows_to_data(&dest_sink.input()));
        }
    }
});

define_test!(field_sensitivity: ctrl -> {
    // Tests that when we stuff two piece of data into a struct
    // they are tracked separately and if we pull them back out they
    // are independent.
    //
    // I'm sorry for how elaborate this test case is.
    // The machinery here is just to distinguish the "used"
    // and "unused" "read_usize" call sites.
    let produce_usize_fn = ctrl.function("produce_usize");
    let produce_string_fn = ctrl.function("produce_string");
    let consume_usize_fn = ctrl.function("read_usize");
    let consume_string_fn = ctrl.function("read_string");
    let produce_usize = ctrl.call_site(&produce_usize_fn);
    let produce_string = ctrl.call_site(&produce_string_fn);
    let read_string = ctrl.call_site(&consume_string_fn);
    let read_usizes = ctrl.call_sites(&consume_usize_fn);

    #[derive(Eq, PartialEq, Copy, Clone)]
    enum CallSiteState {
        Unknow, Distraction, Checked
    }

    use CallSiteState::*;

    let mut usize_call_sites = [Unknow;2];
    for (idx, read_usize) in read_usizes.iter().enumerate() {
        usize_call_sites[idx] = if produce_usize.output().flows_to_data(&read_usize.input()) {
            Checked
        } else {
            Distraction
        };
    }
    assert!(!produce_usize.output().flows_to_data(&read_string.input()));
    assert!(produce_string.output().flows_to_data(&read_string.input()));
    assert!(usize_call_sites.contains(&Distraction));
    assert!(usize_call_sites.contains(&Checked));
});

define_test!(unused_labels skip "": graph, field_sensitivity -> {
    assert!(graph.has_marker("otherwise_unused"));
});

define_test!(field_sensitivity_across_clone: ctrl -> {
    // Tests that when we stuff two piece of data into a struct
    // they are tracked separately and if we pull them back out they
    // are independent, even if the data structure is "clone()"d in
    // between.
    //
    // Similar to the "field_sensitivity" test case.
    //
    // I'm sorry for how elaborate this test case is.
    // The machinery here is just to distinguish the "used"
    // and "unused" "read_usize" call sites.
    let produce_usize_fn = ctrl.function("produce_usize");
    let produce_string_fn = ctrl.function("produce_string");
    let consume_usize_fn = ctrl.function("read_usize");
    let consume_string_fn = ctrl.function("read_string");
    let produce_usize = ctrl.call_site(&produce_usize_fn);
    let produce_string = ctrl.call_site(&produce_string_fn);
    let read_string = ctrl.call_site(&consume_string_fn);
    let read_usizes = ctrl.call_sites(&consume_usize_fn);

    #[derive(Eq, PartialEq, Copy, Clone)]
    enum CallSiteState {
        Unknow, Distraction, Checked
    }

    use CallSiteState::*;

    let mut usize_call_sites = [Unknow;2];
    for (idx, read_usize) in read_usizes.iter().enumerate() {
        usize_call_sites[idx] = if produce_usize.output().flows_to_data(&read_usize.input()) {
            assert!(!produce_string.output().flows_to_data(&read_usize.input()));
            Checked
        } else {
            Distraction
        };
    }
    assert!(!produce_usize.output().flows_to_data(&read_string.input()));
    assert!(produce_string.output().flows_to_data(&read_string.input()));
});

define_test!(no_overtaint_over_fn_call
    skip
    "Field level precision across function calls is broken.
    See https://github.com/willcrichton/flowistry/issues/94."
    : graph -> {
    let input_fn = graph.function("input");
    let input = graph.call_site(&input_fn);
    let another_input_fn = graph.function("source");
    let another_input = graph.call_site(&another_input_fn);

    let target_fn = graph.function("target");
    let target = graph.call_site(&target_fn);
    let another_target_fn = graph.function("another_target");
    let another_target = graph.call_site(&another_target_fn);

    assert!(input.output().flows_to_data(&target.input()));
    assert!(another_input.output().flows_to_data(&another_target.input()));
    assert!(!dbg!(input.output()).flows_to_data(&dbg!(another_target.input())));
    assert!(!another_input.output().flows_to_data(&target.input()));
});

define_test!(no_overtaint_over_generic_fn_call
    skip
    "Field level precision across function calls is broken.
    See https://github.com/willcrichton/flowistry/issues/94."
    : graph -> {
    let input_fn = graph.function("input");
    let input = graph.call_site(&input_fn);
    let another_input_fn = graph.function("source");
    let another_input = graph.call_site(&another_input_fn);

    let target_fn = graph.function("target");
    let target = graph.call_site(&target_fn);
    let another_target_fn = graph.function("another_target");
    let another_target = graph.call_site(&another_target_fn);

    assert!(input.output().flows_to_data(&target.input()));
    assert!(another_input.output().flows_to_data(&another_target.input()));
    assert!(!dbg!(input.output()).flows_to_data(&dbg!(another_target.input())));
    assert!(!another_input.output().flows_to_data(&target.input()));
});

define_test!(no_overtaint_over_nested_fn_call
    skip
    "Field level precision across function calls is broken.
    See https://github.com/willcrichton/flowistry/issues/94."
    : graph -> {
    let input_fn = graph.function("input");
    let input = graph.call_site(&input_fn);
    let another_input_fn = graph.function("source");
    let another_input = graph.call_site(&another_input_fn);

    let target_fn = graph.function("target");
    let target = graph.call_site(&target_fn);
    let another_target_fn = graph.function("another_target");
    let another_target = graph.call_site(&another_target_fn);

    assert!(input.output().flows_to_data(&target.input()));
    assert!(another_input.output().flows_to_data(&another_target.input()));
    assert!(!dbg!(input.output()).flows_to_data(&dbg!(another_target.input())));
    assert!(!another_input.output().flows_to_data(&target.input()));

});

#[test]
fn recursion_breaking_with_k_depth() {
    let mut test = InlineTestBuilder::new(stringify!(
        fn recurses(i: u32) {
            if i > 0 {
                recurses(i - 1);
            }
        }

        #[paralegal_flow::analyze]
        fn main() {
            recurses(10);
        }
    ));
    test.with_extra_args(["--k-depth=3".to_string()])
        .run_with_tcx(|tcx, desc| {
            let ctrl = desc.ctrl("main");
            let css = ctrl.graph().desc.all_call_sites();
            assert!(!css.is_empty(), "Vacuous");
            let target = Symbol::intern("recurses");
            for cs in css.into_iter() {
                assert!(
                    cs.len() <= 4,
                    "Call string over length limit (length {}) {cs} ",
                    cs.len()
                );
                let recursions: Box<[GlobalLocation]> = cs
                    .iter()
                    .filter(|loc| tcx.item_name(loc.function) == target)
                    .collect();
                assert!(
                    recursions.len() <= 1,
                    "Found recursive call strings: {}",
                    display_list(recursions.iter())
                );
                assert!(
                    cs.len() <= 2,
                    "Call string indicates recursion (length {}) {cs}",
                    cs.len()
                );
            }
        })
        .unwrap();
}

#[test]
fn recursion_breaking_with_k_depth_on_main() {
    let mut test = InlineTestBuilder::new(stringify!(
        #[paralegal_flow::analyze]
        fn recurses(i: u32) {
            if i > 0 {
                recurses(i - 1);
            }
        }
    ));
    test.with_extra_args(["--k-depth=1".to_string()])
        .with_entrypoint("recurses".to_string())
        .run_with_tcx(|tcx, desc| {
            let ctrl = desc.ctrl("recurses");
            let css = ctrl.graph().desc.all_call_sites();
            let target = Symbol::intern("recurses");
            assert!(!css.is_empty(), "Vacuous");
            for cs in css.into_iter() {
                assert!(
                    cs.len() <= 2,
                    "Call string over length limit (length {}) {cs} ",
                    cs.len()
                );

                let recursions: Box<[GlobalLocation]> = cs
                    .iter()
                    .filter(|loc| tcx.item_name(loc.function) == target)
                    .collect();
                assert!(
                    recursions.len() <= 1,
                    "Found recursive call strings: {}",
                    display_list(recursions.iter())
                );
                assert!(
                    cs.len() <= 1,
                    "Call string indicates recursion (length {}) {cs}",
                    cs.len()
                );
            }
        })
        .unwrap()
}

#[test]
fn recursion_breaking_with_k_depth_mutual() {
    let mut test = InlineTestBuilder::new(stringify!(
        fn recurses(i: u32) {
            if i > 0 {
                delegator(i);
            }
        }

        fn delegator(i: u32) {
            recurses(i - 1);
        }

        #[paralegal_flow::analyze]
        fn main() {
            recurses(10);
        }
    ));
    test.with_extra_args(["--k-depth=4".to_string()])
        .run_with_tcx(|tcx, desc| {
            let ctrl = desc.ctrl("main");
            let css = ctrl.graph().desc.all_call_sites();
            assert!(!css.is_empty(), "Vacuous");
            let target = Symbol::intern("recurses");
            for cs in css.into_iter() {
                assert!(
                    cs.len() <= 5,
                    "Call string over length limit (length {}) {cs} ",
                    cs.len()
                );
                let recursions: Box<[GlobalLocation]> = cs
                    .iter()
                    .filter(|loc| tcx.item_name(loc.function) == target)
                    .collect();
                assert!(
                    recursions.len() <= 1,
                    "Found recursive call strings: {} in {cs}",
                    display_list(recursions.iter())
                );
                assert!(
                    cs.len() <= 3,
                    "Call string indicates recursion (length {}) {cs}",
                    cs.len()
                );
            }
        })
        .unwrap();
}
