use paralegal_flow::{ann::db::AutoMarkers, define_flow_test_template, inline_test, test_utils::*};

const TEST_CRATE_NAME: &str = "tests/purity/test-crate";
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

define_test!(side_effect_tcp: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(side_effect_pure: ctrl -> {
    ctrl.assert_purity(true);
});

define_test!(side_effect_extern: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(side_effect_extern_flow: ctrl -> {
    let auto_markers = AutoMarkers::new();
    ctrl.assert_purity(false);

    let source1 = ctrl.marked("source");
    let source2 = ctrl.marked("source2");
    let side_effecting: NodeRefs = auto_markers
        .all()
        .iter()
        .flat_map(|m| ctrl.marked(*m))
        .collect();
    assert!(!source1.is_empty());
    assert!(!source2.is_empty());
    assert!(!side_effecting.is_empty());

    assert!(source1.flows_to_data(&side_effecting));
    assert!(!source2.flows_to_data(&side_effecting));
});

fn tcp_flow_check(ctrl: CtrlRef<'_>) {
    let auto_markers = AutoMarkers::new();
    let defined = dbg!(ctrl.markers());
    let auto = auto_markers.all();
    let contained = dbg!(auto
        .iter()
        .filter(|m| defined.contains(m))
        .collect::<Vec<_>>());
    assert!(!contained.is_empty());

    let source1 = ctrl.marked("source");
    let source2 = ctrl.marked("source2");
    let side_effecting: NodeRefs = auto_markers
        .all()
        .iter()
        .flat_map(|m| ctrl.marked(*m))
        .collect();
    assert!(!source1.is_empty());
    assert!(!source2.is_empty());
    assert!(!side_effecting.is_empty());

    assert!(source1.flows_to_data(&side_effecting));
    assert!(!source2.flows_to_data(&side_effecting));
}

define_test!(side_effect_tcp_flow: ctrl -> {
    tcp_flow_check(ctrl);
});

define_test!(side_effect_vec: ctrl -> {
    ctrl.assert_purity(true);
});
