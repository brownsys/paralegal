use paralegal_flow::inline_test;
use paralegal_flow::test_utils::HasGraph;

#[test]
#[ignore = "Paralegal cannot resolve function pointers."]
fn fn_ptr_coercion() {
    inline_test! {
    #[paralegal_flow::analyze]
    pub fn foo(data: usize) -> usize {
        data + 1
    }

    #[paralegal_flow::analyze]
    pub fn fn_to_fn_ptr(data: usize) -> usize {
        let fn_ptr: fn(usize) -> usize = foo;
        fn_ptr(data)
    }
    }
    .without_entrypoint()
    .with_extra_args(["--side-effect-markers"])
    .run(|graphs| {
        graphs.ctrl("foo").assert_purity(true);
        graphs.ctrl("fn_to_fn_ptr").assert_purity(true);
    })
    .unwrap()
}

#[test]
fn fmt() {
    inline_test! {
        pub fn main(data: usize) -> String {
            format!("{}", data)
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(true));
}
