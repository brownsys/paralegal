#![feature(rustc_private)]

use paralegal_flow::test_utils::InlineTestBuilder;

#[test]
fn basic_external_entrypoint_test() {
    InlineTestBuilder::new(stringify!(
        fn target() {}
    ))
    .with_entrypoint("crate::target")
    .check_ctrl(|_| {});
}

#[test]
fn trait_instance_entry_point_test() {
    InlineTestBuilder::new(stringify!(
        struct MyStruct {}

        impl Clone for MyStruct {
            fn clone(&self) -> Self {
                MyStruct {}
            }
        }
    ))
    .with_entrypoint("<crate::MyStruct as std::clone::Clone>::clone")
    .run(|graph| {
        assert!(graph
            .desc
            .controllers
            .values()
            .any(|v| v.name.as_str() == "clone"))
    })
    .unwrap()
}

#[test]
fn qualified_type_without_trait() {
    InlineTestBuilder::new(stringify!(
        struct MyStruct {}

        impl MyStruct {
            fn method(&self) {}
        }
    ))
    .with_entrypoint("<crate::MyStruct>::method")
    .run(|graph| {
        assert!(graph
            .desc
            .controllers
            .values()
            .any(|v| v.name.as_str() == "method"))
    })
    .unwrap()
}

#[test]
fn reject_generic_arguments_test() {
    InlineTestBuilder::new(stringify!(
        struct MyStruct<T>(Vec<T>);

        impl Clone for MyStruct<usize> {
            fn clone(&self) -> Self {
                MyStruct(self.0.clone())
            }
        }
    ))
    .with_entrypoint("<crate::MyStruct<usize> as std::clone::Clone>::clone")
    .expect_fail_compile()
}
