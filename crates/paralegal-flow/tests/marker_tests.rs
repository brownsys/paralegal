#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

use paralegal_flow::{define_flow_test_template, test_utils::*};
use paralegal_spdg::{Identifier, InstructionKind};

const TEST_CRATE_NAME: &str = "tests/marker-tests";
const EXTRA_ARGS: &[&str] = &["--no-cross-function-analysis"];

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool =
        run_paralegal_flow_with_flow_graph_dump_and(TEST_CRATE_NAME, EXTRA_ARGS);
}

macro_rules! define_test {
    ($($t:tt)*) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, TEST_CRATE_NAME, $($t)*);
    };
}

#[test]
fn use_wrapper() {
    InlineTestBuilder::new(stringify! {
        #[paralegal_flow::marker(wrapper)]
        pub struct Wrapper<T: ?Sized>(T);

        fn make_wrapper() -> Result<std::sync::Arc<Wrapper<u32>>, String> {
            unimplemented!()
        }

        fn consume_any<T>(w: T) {
            unimplemented!()
        }
        fn main() {
            consume_any(make_wrapper())
        }
    })
    .with_extra_args(EXTRA_ARGS.iter().map(|s| s.to_string()))
    .check_ctrl(|ctrl| {
        let uwf = ctrl.function("make_wrapper");
        let cs = ctrl.call_site(&uwf);
        println!("{:?}", &ctrl.graph().desc.type_info);
        println!("{:?}", ctrl.spdg().type_assigns);
        let tp = cs.output().as_singles().any(|n| {
            dbg!(ctrl.types_for(n.node())).iter().any(|t| {
                ctrl.graph().desc.type_info[t]
                    .rendering
                    .contains("::Wrapper")
            })
        });
        assert!(tp, "Type not found on method");
    });
}

define_test!(trait_method_marker: ctrl -> {
    let marker = Identifier::new_intern("find_me");
    for method in ctrl.functions("method") {
        let spdg = ctrl.spdg();
        assert!(spdg.markers
            .iter()
            .any(|(node, markers)| {
                let weight = spdg.graph.node_weight(*node).unwrap();
                !matches!(ctrl.graph().desc.instruction_info[&weight.at.leaf()].kind,
                    InstructionKind::FunctionCall(fun) if fun.id == method.ident)
                || markers.contains(&marker)
            }));
    }
});

define_test!(wrapping_typed_input: ctrl -> {
    let marker = Identifier::new_intern("wrapper");
    assert!(ctrl.spdg().arguments.iter().any(|node| {
        let ts = ctrl.spdg().node_types(*node);
        dbg!(ts).iter().any(|t| {
            ctrl.graph().desc.type_info[t].markers.contains(&marker)
        })
    }))
});

define_test!(typed_input: ctrl -> {
    let marker = Identifier::new_intern("marked");
    assert!(ctrl.spdg().arguments.iter().any(|node| {
        let ts = ctrl.spdg().node_types(*node);
        dbg!(ts).iter().any(|t| {
            ctrl.graph().desc.type_info[t].markers.contains(&marker)
        })
    }))
});

define_test!(typed_input_zst: ctrl -> {
    let marker = Identifier::new_intern("marked");
    assert!(ctrl.spdg().arguments.iter().any(|node| {
        let ts = ctrl.spdg().node_types(*node);
        dbg!(ts).iter().any(|t| {
            ctrl.graph().desc.type_info[t].markers.contains(&marker)
        })
    }))
});
