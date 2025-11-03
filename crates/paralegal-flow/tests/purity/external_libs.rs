use paralegal_flow::{ann::db::AutoMarkers, define_flow_test_template, test_utils::*};

const TEST_CRATE_NAME: &str = "tests/purity/test-crate-external-libs";
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

define_test!(date_format: ctrl -> {
    ctrl.assert_purity(true);
});
