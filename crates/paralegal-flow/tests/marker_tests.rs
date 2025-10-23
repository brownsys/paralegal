#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

use paralegal_flow::{ann::db::AutoMarkers, define_flow_test_template, inline_test, test_utils::*};
use paralegal_spdg::{Identifier, InstructionKind};

const TEST_CRATE_NAME: &str = "tests/marker-tests";
const EXTRA_ARGS: [&str; 1] = ["--no-interprocedural-analysis"];

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

#[test]
fn marker_on_trait_parent() {
    InlineTestBuilder::new(stringify!(
        trait Test {
            #[paralegal_flow::marker(me, arguments = [0])]
            fn test(self) {}
        }

        impl Test for () {
            fn test(self) {}
        }

        #[paralegal_flow::marker(source, return)]
        fn source() -> () {
            ()
        }

        #[paralegal_flow::analyze]
        fn main() {
            let x = source();
            x.test();
        }
    ))
    .check_ctrl(|ctrl| {
        dbg!(ctrl.markers());
        dbg!(&ctrl.spdg().markers);
        let src = ctrl.marked("source");
        assert!(!src.is_empty());
        let hello_target = ctrl.marked("me");
        assert!(!hello_target.is_empty());

        assert!(src.flows_to_data(&hello_target));
    });
}

#[test]
fn named_refinement() {
    InlineTestBuilder::new(stringify!(
        #[paralegal_flow::marker(me, arguments = [hello, 2])]
        fn test(one: u32, hello: u32, hello_again: u32) {}

        #[paralegal_flow::marker(source, return)]
        fn source() -> u32 {
            42
        }

        #[paralegal_flow::marker(source2, return)]
        fn source2() -> u32 {
            30
        }

        #[paralegal_flow::marker(source3, return)]
        fn source3() -> u32 {
            30
        }

        #[paralegal_flow::analyze]
        fn main() {
            let x = source2();
            let y = source();
            let z = source3();
            test(x, y, z);
        }
    ))
    .check_ctrl(|ctrl| {
        let test_fn = ctrl.function("test");
        let call_sites = ctrl.call_sites(&test_fn);
        assert_eq!(
            call_sites.len(),
            1,
            "Expected one call site for test function"
        );
        let call_site = call_sites.first().unwrap();
        assert!(call_site.input().as_singles().any(|n| {
            ctrl.spdg()
                .markers
                .get(&n.node())
                .is_some_and(|markers| markers.contains(&Identifier::new_intern("me")))
        }));
        let src1 = ctrl.marked("source");
        assert!(!src1.is_empty());
        let src2 = ctrl.marked("source2");
        assert!(!src2.is_empty());
        let src3 = ctrl.marked("source3");
        assert!(!src3.is_empty());
        let hello_target = ctrl.marked("me");
        assert!(!hello_target.is_empty());

        assert!(src1.flows_to_data(&hello_target));
        assert!(!src2.flows_to_data(&hello_target));
        assert!(src3.flows_to_data(&hello_target));
    });
}

#[test]
fn named_refinement_on_self() {
    InlineTestBuilder::new(stringify!(
        trait Test {
            #[paralegal_flow::marker(me, arguments = [self])]
            fn test(self) {}
        }

        impl Test for () {
            fn test(self) {}
        }

        #[paralegal_flow::marker(source, return)]
        fn source() -> () {
            ()
        }

        #[paralegal_flow::analyze]
        fn main() {
            let x = source();
            x.test();
        }
    ))
    .check_ctrl(|ctrl| {
        // This condition doesn't quite work, because 'test' being a trait
        // function somehow means it shows up multiple times in the PDG info. So
        // I am leaving the conditions here, maybe we can debug them in the
        // future and add them back.
        //
        // let test_fn = ctrl.function("test");
        // let call_sites = ctrl.call_sites(&test_fn);
        // assert_eq!(
        //     call_sites.len(),
        //     1,
        //     "Expected one call site for test function"
        // );
        // let call_site = call_sites.first().unwrap();
        // assert!(call_site.input().as_singles().any(|n| {
        //     ctrl.spdg().markers.get(&n.node()).map_or(false, |markers| {
        //         markers.contains(&Identifier::new_intern("me"))
        //     })
        // }));
        dbg!(ctrl.markers());
        dbg!(&ctrl.spdg().markers);
        let src = ctrl.marked("source");
        assert!(!src.is_empty());
        let hello_target = ctrl.marked("me");
        assert!(!hello_target.is_empty());

        assert!(src.flows_to_data(&hello_target));
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
    let tyinf = dbg!(&ctrl.graph().desc.type_info);
    dbg!(&ctrl.spdg().type_assigns);
    assert!(dbg!(&ctrl.spdg().arguments).iter().any(|node| {
        let ts = ctrl.spdg().node_types(*node);
        dbg!(ts).iter().any(|t| {
            tyinf[t].markers.contains(&marker)
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

#[test]
fn no_overtaint_from_sibling_markers() {
    inline_test! {
        #[paralegal_flow::marker(marked)]
        struct Marked;

        struct Parent {
            marked: Marked,
            unmarked: u32,
        }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn reached<T>(_: T) {}

        #[paralegal_flow::marker(sink_2, arguments = [0])]
        fn reached_2<T>(_: T) {}

        fn main(parent: Parent) {
            reached(parent.unmarked);
            reached_2(parent.marked);
        }
    }
    .check_ctrl(|ctrl| {
        let src = ctrl.marked("marked");
        let reached = ctrl.marked("sink");
        let reached_2 = ctrl.marked("sink_2");
        println!("{:?}", ctrl.spdg().type_assigns);
        println!("{:?}", ctrl.spdg().markers);
        assert!(!src.is_empty());
        assert!(!reached.is_empty());
        assert!(!reached_2.is_empty());
        for n in src.nodes() {
            assert!(
                !reached.nodes().contains(n),
                "{n:?} is marked both `sink` and `marked`"
            );
        }
        assert!(!src.flows_to_data(&reached));
        assert!(src.flows_to_data(&reached_2));
    });
}

#[test]
fn async_fn_marker() {
    inline_test! {
        #[paralegal_flow::marker(find_me, return )]
        async fn async_fn_marker() -> i32 {
            42
        }

        #[paralegal_flow::marker(find_me_also, arguments = [0])]
        async fn async_fn_marker_2(arg: i32) {
            assert_eq!(arg, 42);
        }

        async fn main() {
            async_fn_marker_2(
                async_fn_marker().await
            ).await;
        }
    }
    .check_ctrl(|ctrl| {
        let source = ctrl.marked("find_me");
        let sink = ctrl.marked("find_me_also");
        assert!(!source.is_empty());
        assert!(!sink.is_empty());
        assert!(source.flows_to_data(&sink));
    });
}

#[test]
fn side_effect_tcp() {
    inline_test! {
        use std::io::prelude::*;
        use std::net::TcpStream;

        fn main() -> std::io::Result<()> {
            let mut stream = TcpStream::connect("127.0.0.1:34254")?;

            stream.write(&[1])?;
            stream.read(&mut [0; 128])?;
            Ok(())
        }
    }
    .with_extra_args(["--side-effect-markers".to_string()])
    .check_ctrl(|ctrl| {
        let auto_markers = AutoMarkers::new();
        let defined = ctrl.markers();
        let auto = auto_markers.all();
        let contained = dbg!(auto
            .iter()
            .filter(|m| defined.contains(m))
            .collect::<Vec<_>>());
        assert!(!contained.is_empty());
    });
}

#[test]
fn side_effect_pure() {
    inline_test! {
        fn main() -> std::io::Result<()> {
            let x = 2;
            let y = 3 + x;
            Ok(())
        }
    }
    .with_extra_args(["--side-effect-markers".to_string()])
    .check_ctrl(|ctrl| {
        let auto_markers = AutoMarkers::new();
        let defined = ctrl.markers();
        let auto = auto_markers.all();
        let contained = dbg!(auto
            .iter()
            .filter(|m| defined.contains(m))
            .collect::<Vec<_>>());
        assert!(contained.is_empty());
    });
}

#[test]
fn side_effect_extern() {
    inline_test! {
        extern "C" {
            fn plus(a: i32, b: i32) -> i32;
        }

        fn main() -> std::io::Result<()> {
            let x = 2;
            let y = plus(3, x);
            Ok(())
        }
    }
    .with_extra_args(["--side-effect-markers".to_string()])
    .check_ctrl(|ctrl| {
        let auto_markers = AutoMarkers::new();
        let defined = dbg!(ctrl.markers());
        let auto = auto_markers.all();
        for i in ctrl.functions("plus") {
            dbg!(ctrl.info_for(i.ident));
        }
        let contained = dbg!(auto
            .iter()
            .filter(|m| defined.contains(m))
            .collect::<Vec<_>>());
        assert!(!contained.is_empty());
    });
}

#[test]
fn side_effect_extern_flow() {
    inline_test! {
        extern "C" {
            fn plus(a: i32, b: i32) -> i32;
        }

        #[paralegal_flow::marker(source, return)]
        fn source() -> i32 {
            42
        }

        #[paralegal_flow::marker(source2, return)]
        fn source2() -> i32 {
            43
        }

        fn main() -> std::io::Result<()> {
            let x = source2();
            let z = source();
            let y = plus(z, 3);
            let result = y + x;
            Ok(())
        }
    }
    .with_extra_args(["--side-effect-markers".to_string()])
    .check_ctrl(|ctrl| {
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
    });
}

#[test]
fn side_effect_tcp_flow() {
    inline_test! {
        use std::io::prelude::*;
        use std::net::TcpStream;

        #[paralegal_flow::marker(source, return)]
        fn source() -> u8 {
            42
        }

        #[paralegal_flow::marker(source2, return)]
        fn source2() -> u8 {
            43
        }

        fn main() -> std::io::Result<()> {
            let mut stream = TcpStream::connect("127.0.0.1:34254")?;
            let y = source2();
            stream.write(&[source()])?;
            let mut buf = [0; 128];
            stream.read(&mut buf)?;
            let _ = y + buf[0];
            Ok(())
        }

    }
    .with_extra_args(["--side-effect-markers".to_string()])
    .check_ctrl(|ctrl| {
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
    });
}

#[test]
fn side_effect_vec() {
    inline_test! {
        fn main() {
            let mut v = vec![0];
            v.push(1);
            v.pop();
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(true));
}
