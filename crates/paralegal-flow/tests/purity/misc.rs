use paralegal_flow::{ann::db::AutoMarkers, inline_test, test_utils::*};
use paralegal_spdg::DisplayPath;

const STDLIB_MARKERS: &str = include_str!("./stdlib-markers.toml");

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
    .with_dependencies()
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn side_effect_empty() {
    inline_test! {
        fn main() -> std::io::Result<()> {
            Ok(())
        }
    }
    .with_dependencies()
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
    });
}

#[test]
fn side_effect_add() {
    inline_test! {
        fn main() -> std::io::Result<()> {
            let x = 2;
            let y = 3 + x;
            Ok(())
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
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
            let y = unsafe { plus(3, x) };
            Ok(())
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
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
            let y = unsafe { plus(z, 3) };
            let result = y + x;
            Ok(())
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
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
}

#[test]
fn side_effect_tcp_flow() {
    inline_test! {
        use std::io::prelude::*;
        use std::net::TcpStream;

        #[paralegal_flow::marker(source, return)]
        fn tcp_source() -> u8 {
            42
        }

        #[paralegal_flow::marker(source2, return)]
        fn tcp_source2() -> u8 {
            43
        }

        fn main() -> std::io::Result<()> {
            let mut stream = TcpStream::connect("127.0.0.1:34254")?;
            let y = tcp_source2();
            stream.write(&[tcp_source()])?;
            let mut buf = [0; 128];
            stream.read(&mut buf)?;
            let _ = y + buf[0];
            Ok(())
        }
    }
    .with_dependencies()
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        let auto_markers = AutoMarkers::default();
        let defined = dbg!(ctrl.markers());
        let auto = auto_markers.all();
        let contained = dbg!(
            auto.iter()
                .filter(|m| defined.contains(m))
                .collect::<Vec<_>>()
        );
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
    .with_dependencies()
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        let auto_markers = AutoMarkers::default();
        let auto = auto_markers.all();
        for m in auto {
            let marked = ctrl.marked(m);
            if !marked.is_empty() {
                println!("Side effect {m}");
            }
            for n in marked {
                assert_eq!(n.info().at.root().function, ctrl.id());
                let d = DisplayPath::from(
                    &ctrl.graph().desc.def_info[&n.info().at.leaf().function].path,
                );
                println!(
                    "{} in {} in {}",
                    n.info().kind,
                    n.instruction_info().description,
                    d
                );
            }
        }
        ctrl.assert_purity(true);
    });
}

#[test]
fn closure_tests() {
    inline_test! {
        #[inline(never)]
        pub fn execute_once<F: FnOnce(usize) -> usize>(x: usize, l: F) -> usize {
            l(x)
        }

        #[inline(never)]
        pub fn execute_mut<F: FnMut(usize) -> usize>(x: usize, mut l: F) -> usize {
            l(x)
        }

        #[inline(never)]
        pub fn execute<F: Fn(usize) -> usize>(x: usize, l: F) -> usize {
            l(x)
        }

        fn main() {
            let a = 10usize;
            let lambda = |x: usize| -> usize {
                return x * x;
            };

            let capture_param = 42;
            let closure_capture = |x: usize| -> usize {
                return x * capture_param;
            };

            let capture_move_param = 42;
            let closure_capture_move = move |x: usize| -> usize {
                return x * capture_move_param;
            };

            let ambiguous_lambda = if a > 5 {
                |x: usize| -> usize {
                    return x;
                }
            } else {
                |x: usize| -> usize {
                    return x * x;
                }
            };

            execute_once(a, lambda);
            execute_once(a, closure_capture);
            execute_once(a, closure_capture_move);
            execute_once(a, ambiguous_lambda);

            execute_mut(a, lambda);
            execute_mut(a, closure_capture);
            execute_mut(a, closure_capture_move);
            execute_mut(a, ambiguous_lambda);

            execute(a, lambda);
            execute(a, closure_capture);
            execute(a, closure_capture_move);
            execute(a, ambiguous_lambda);
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
    });
}

#[test]
fn annotation_test_impl_pure() {
    inline_test! {
        extern "C" {
            fn foo() -> i32;
        }

        struct MyStruct;

        impl MyStruct {
            #[paralegal_flow::marker(trusted)]
            pub fn bar() -> i32 {
                unsafe { foo() }
            }
        }

        fn main() {
            MyStruct::bar();
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
    });
}

#[test]
fn annotation_test_impl_impure() {
    inline_test! {
        extern "C" {
            fn foo() -> i32;
        }

        struct OtherStruct;

        impl OtherStruct {
            pub fn bar() -> i32 {
                unsafe { foo() }
            }
        }

        fn main() {
            OtherStruct::bar();
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn annotation_test_mod_pure() {
    inline_test! {
        mod my_mod {
            extern "C" {
                fn foo() -> i32;
            }

            #[paralegal_flow::marker(trusted)]
            pub fn bar() -> i32 {
                unsafe { foo() }
            }
        }

        fn main() {
            my_mod::bar();
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
    });
}

#[test]
fn annotation_test_mod_impure() {
    inline_test! {
        mod other_mod {
            extern "C" {
                fn foo() -> i32;
            }

            pub fn bar() -> i32 {
                unsafe { foo() }
            }
        }

        fn main() {
            other_mod::bar();
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn annotation_test_nested_impl_pure() {
    inline_test! {
        mod my_mod {
            extern "C" {
                fn foo() -> i32;
            }

            pub struct NestedStruct;

            impl NestedStruct {
                #[paralegal_flow::marker(trusted)]
                pub fn bar() -> i32 {
                    unsafe { foo() }
                }
            }
        }

        fn main() {
            my_mod::NestedStruct::bar();
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
    });
}

#[test]
fn annotation_test_nested_impl_impure() {
    inline_test! {
        mod other_mod {
            extern "C" {
                fn foo() -> i32;
            }

            pub struct NestedStruct;

            impl NestedStruct {
                pub fn bar() -> i32 {
                    unsafe { foo() }
                }
            }
        }

        fn main() {
            other_mod::NestedStruct::bar();
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn clone_unit_test() {
    inline_test! {
        fn main() {
            ().clone()
        }
    }
    .with_dependencies()
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
        assert!(ctrl.has_function("clone"));
    });
}

#[test]
fn clone_unit_test_wrapped() {
    inline_test! {
        fn wrapper() {
            ().clone()
        }

        fn main() {
            wrapper()
        }
    }
    .with_dependencies()
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
        assert!(!ctrl.has_function("clone"));
    });
}

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
    .with_dependencies()
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        for n in ctrl.side_effect_nodes() {
            println!("Side effect node: {n:?}");
        }
        assert!(!ctrl.has_function("clone"));
    });
}

#[test]
fn structs() {
    inline_test! {
        struct Foo {
            a: usize,
            b: &'static str,
            c: bool,
        }

        fn main() {
            let a = 5usize;
            let mut foo = Foo {
                a,
                b: "hello",
                c: true,
            };
            foo.a = 30;
            foo.b = "hello2";
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
    });
}
