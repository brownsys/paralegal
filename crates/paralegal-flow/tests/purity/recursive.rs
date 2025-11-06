use paralegal_flow::define_flow_test_template;
use paralegal_flow::test_utils::*;

const TEST_CRATE_NAME: &str = "tests/purity/test-crate-recursive";
const EXTRA_ARGS: &[&str] = &[
    "--side-effect-markers",
    // "--external-annotations",
    // "../stdlib-markers.toml",
];

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool =
        run_paralegal_flow_with_flow_graph_dump_and(TEST_CRATE_NAME, EXTRA_ARGS);
}

macro_rules! define_test {
    ($($t:tt)*) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, TEST_CRATE_NAME, $($t)*);
    };
}

define_test!(pure: ctrl -> {
    ctrl.assert_purity(true);
});

define_test!(impure: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(mutually_recursive_pure_1: ctrl -> {
    ctrl.assert_purity(true);
});

define_test!(mutually_recursive_pure_2: ctrl -> {
    ctrl.assert_purity(true);
});

define_test!(mutually_recursive_impure_1: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(mutually_recursive_impure_2: ctrl -> {
    ctrl.assert_purity(false);
});
