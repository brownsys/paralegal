use paralegal_flow::{ann::db::AutoMarkers, define_flow_test_template, inline_test, test_utils::*};
use paralegal_spdg::DisplayPath;

const TEST_CRATE_NAME: &str = "tests/purity/test-crate-misc";
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

define_test!(side_effect_tcp: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(side_effect_empty: ctrl -> {
    ctrl.assert_purity(true);
});

define_test!(side_effect_add: ctrl -> {
    ctrl.assert_purity(true);
});

define_test!(side_effect_extern: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(side_effect_extern_flow: ctrl -> {
    let auto_markers = AutoMarkers::default();
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
    let auto_markers = AutoMarkers::default();
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

    let auto_markers = AutoMarkers::default();
    let auto = auto_markers.all();
    for m in auto {
        let marked = ctrl.marked(m);
        if !marked.is_empty() {
            println!("Side effect {m}");
        }
        for n in marked {
            assert_eq!(n.info().at.root().function, ctrl.id());
            let d = DisplayPath::from(&ctrl.graph().desc.def_info[&n.info().at.leaf().function].path);
            println!("{} in {} in {}", n.info().kind, n.instruction_info().description, d);
        }

    }
    ctrl.assert_purity(true);
});

define_test!(closure_tests: ctrl -> {
    ctrl.assert_purity(true);
});

define_test!(annotation_test_impl_pure: ctrl -> {
   ctrl.assert_purity(true);
});

define_test!(annotation_test_impl_impure: ctrl -> {
   ctrl.assert_purity(false);
});

define_test!(annotation_test_mod_pure: ctrl -> {
    ctrl.assert_purity(true);
});

define_test!(annotation_test_mod_impure: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(annotation_test_nested_impl_pure: ctrl -> {
    ctrl.assert_purity(true);
});

define_test!(annotation_test_nested_impl_impure: ctrl -> {
    ctrl.assert_purity(false);
});

define_test!(clone_unit_test: ctrl -> {
    ctrl.assert_purity(true);
    assert!(ctrl.has_function("clone"));
});

define_test!(clone_unit_test_wrapped: ctrl -> {
    ctrl.assert_purity(true);
    assert!(!ctrl.has_function("clone"));
});

#[test]
fn clone_test_reachability() {
    inline_test! {
        fn wrapper() {
            ().clone();
        }

        fn main() {
            wrapper();
        }
    }
    .check_ctrl(|ctrl| {
        for n in ctrl.side_effect_nodes() {
            println!("Side effect node: {n:?}");
        }
        assert!(!ctrl.has_function("clone"));
    });
}

define_test!(structs: ctrl -> {
    ctrl.assert_purity(true);
});
