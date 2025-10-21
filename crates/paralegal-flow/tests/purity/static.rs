use paralegal_flow::inline_test;
use paralegal_flow::test_utils::HasGraph;

#[test]
fn mutable_static() {
    inline_test! {
        static mut GLOBAL_VEC: Vec<u32> = vec![];

        fn main(a: u32) {
            unsafe {
                GLOBAL_VEC.push(a);
            }
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn mutation_from_static() {
    inline_test! {
        struct PureIncrementer;

        impl PureIncrementer {
            fn inc(&self, a: usize) -> usize {
                a + 1
            }
        }

        struct ImpureIncrementer;

        impl ImpureIncrementer {
            fn inc(&self, a: usize) -> usize {
                println!("{}", a);
                a + 1
            }
        }

        static PURE_INCREMENTER: PureIncrementer = PureIncrementer {};
        static IMPURE_INCREMENTER: ImpureIncrementer = ImpureIncrementer {};

        #[paralegal_flow::analyze]
        fn pure_call_from_static(a: usize) -> usize {
            PURE_INCREMENTER.inc(a)
        }

        #[paralegal_flow::analyze]
        fn impure_call_from_static(a: usize) -> usize {
            IMPURE_INCREMENTER.inc(a)
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .without_entrypoint()
    .run(|graphs| {
        graphs.ctrl("pure_call_from_static").assert_purity(true);
        graphs.ctrl("impure_call_from_static").assert_purity(false);
    })
    .unwrap()
}
