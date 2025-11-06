use paralegal_flow::{define_flow_test_template, test_utils::*};

const TEST_CRATE_NAME: &str = "tests/purity/test-crate-leaky";
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

define_test!(print: ctrl -> {
    ctrl.assert_purity(false)
});

define_test!(network: ctrl-> {
    ctrl.assert_purity(false);
});

define_test!(interior: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(implicit
    skip "We don't support this yet"
    : ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(transmute_struct: ctrl -> {
    ctrl.assert_purity(false);
});
define_test!(transmute_arr: ctrl -> {
    ctrl.assert_purity(false);
});
define_test!(intrinsic_leaker: ctrl -> {
    ctrl.assert_purity(false);
});
