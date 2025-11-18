use paralegal_flow::define_flow_test_template;
use paralegal_flow::test_utils::*;

const TEST_CRATE_NAME: &str = "tests/purity/test-crate-side-effect";
const EXTRA_ARGS: &[&str] = &[
    "--side-effect-markers",
    "--external-annotations",
    "../stdlib-markers.toml",
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

define_test!(fs: ctrl -> {
    for (n, m) in ctrl.spdg().markers.iter() {
        let info = ctrl.spdg().node_info(*n);
        let instruction = & ctrl.graph().desc.instruction_info[&info.at.leaf()];
        eprintln!("{} in {} is marked {m:?}", info.kind, instruction.description);
    }

    assert!(!ctrl.marked("side-effect:fs:write").is_empty());
});
