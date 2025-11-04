use paralegal_flow::define_flow_test_template;
use paralegal_flow::test_utils::*;

const TEST_CRATE_NAME: &str = "tests/purity/test-crate-raw-ptr";
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

define_test!(raw_mut_ptr_deref: ctrl ->  {
    ctrl.assert_purity(false);
});

define_test!(raw_mut_ptr_mut_ref: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(raw_mut_ptr_mut_ref_not_in_main: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(raw_mut_ptr_call: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(safe_raw_mut_ptr
    skip "We are more conservative than scrutinizer here and disallow all raw pointers, whether they are mutable or not."
    : ctrl -> {
    ctrl.assert_purity(true);
});

define_test!(raw_const_ptr: ctrl -> {
    ctrl.assert_purity(true);
});
