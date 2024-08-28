use paralegal_flow::test_utils::InlineTestBuilder;

#[test]
fn basic_external_entrypoint_test() {
    InlineTestBuilder::new(stringify!(
        fn target() {}
    ))
    .with_entrypoint("crate::target")
    .check(|_| {});
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
}
