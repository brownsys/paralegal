use paralegal_flow::inline_test;
use paralegal_flow::test_utils::HasGraph;

#[test]
fn self_recursive_pure() {
    inline_test! {
        fn main(a: usize) {
            if a > 0 {
                pure(a - 1);
            }
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(true));
}

#[test]
fn self_recursive_impure() {
    inline_test! {
        fn main(a: usize) {
            if a > 0 {
                impure(a - 1);
            }
            println!("{}", a);
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn mutually_recursive() {
    inline_test! {
        #[paralegal_flow::analyze]
        fn pure_1(a: usize) {
            if a > 0 {
                pure_2(a - 1);
            }
        }

        #[paralegal_flow::analyze]
        fn pure_2(a: usize) {
            if a > 0 {
                pure_1(a - 1);
            }
        }

        #[paralegal_flow::analyze]
        fn impure_1(a: usize) {
            if a > 0 {
                impure_2(a - 1);
            }
            println!("{}", a);
        }

        #[paralegal_flow::analyze]
        fn impure_2(a: usize) {
            if a > 0 {
                impure_1(a - 1);
            }
            println!("{}", a);
        }
    }
    .without_entrypoint()
    .with_extra_args(["--side-effect-markers"])
    .run(|graphs| {
        graphs.ctrl("pure_1").assert_purity(true);
        graphs.ctrl("pure_2").assert_purity(true);
        graphs.ctrl("impure_1").assert_purity(false);
        graphs.ctrl("impure_2").assert_purity(false);
    })
    .unwrap()
}
