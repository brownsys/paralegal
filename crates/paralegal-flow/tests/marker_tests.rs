#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

use paralegal_flow::{define_flow_test_template, test_utils::*};
use paralegal_spdg::{Identifier, InstructionInfo};

const TEST_CRATE_NAME: &str = "tests/marker-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump_and(
        TEST_CRATE_NAME,
        ["--no-cross-function-analysis"]
    );
}

macro_rules! define_test {
    ($name:ident: $ctrl:ident -> $block:block) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, TEST_CRATE_NAME, $name: $ctrl, $name -> $block);
    };
}

define_test!(use_wrapper: ctrl -> {
    let uwf = ctrl.function("make_wrapper");
    let cs = ctrl.call_site(&uwf);
    let types = ctrl.types_for(cs.output().nth(0).unwrap().node());
    assert!(!types.is_empty(), "Type not found on method");
    assert!(
        types.iter().any(|t| ctrl.graph().desc.def_info[t].name.as_str() == "Wrapper"))
});

define_test!(trait_method_marker: ctrl -> {
    let marker = Identifier::new_intern("find_me");
    for method in ctrl.functions("method") {
        let spdg = ctrl.spdg();
        assert!(spdg.markers
            .iter()
            .any(|(node, markers)| {
                let weight = spdg.graph.node_weight(*node).unwrap();
                !matches!(ctrl.graph().desc.instruction_info[&weight.at.leaf()],
                    InstructionInfo::FunctionCall(fun) if fun == method.ident)
                || markers.contains(&marker)
            }));
    }
});
