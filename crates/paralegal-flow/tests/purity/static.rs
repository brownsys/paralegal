use paralegal_flow::{define_flow_test_template, test_utils::*};

const TEST_CRATE_NAME: &str = "tests/purity/test-crate-static";
const EXTRA_ARGS: [&str; 1] = ["--side-effect-markers"];

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool =
        run_paralegal_flow_with_flow_graph_dump_and(TEST_CRATE_NAME, EXTRA_ARGS);
}

macro_rules! define_test {
    ($($t:tt)*) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, TEST_CRATE_NAME, $($t)*);
    };
}

define_test!(mutable_static: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(pure_call_from_static: ctrl -> {
    ctrl.assert_purity(true);
});
define_test!(impure_call_from_static: ctrl -> {
    ctrl.assert_purity(false);
});
