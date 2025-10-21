use paralegal_flow::inline_test;

#[test]
fn structs() {
    inline_test! {
        struct Foo {
            a: usize,
            b: &'static str,
            c: bool,
        }

        fn main(a: usize) {
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
    .check_ctrl(|ctrl| ctrl.assert_purity(true));
}
