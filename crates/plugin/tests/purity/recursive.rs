use paralegal_flow::{inline_test, test_utils::*};

#[test]
fn pure() {
    inline_test! {
        fn pure_fn(a: usize) {
            if a > 0 {
                pure_fn(a - 1);
            }
        }

        fn main() {
            pure_fn(0);
        }
    }
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
    });
}

#[test]
fn impure() {
    inline_test! {
        fn impure_fn(a: usize) {
            if a > 0 {
                impure_fn(a - 1);
            }
            println!("{}", a);
        }

        fn main() {
            impure_fn(0);
        }
    }
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn mutually_recursive_pure_1() {
    inline_test! {
        fn rec_pure_1(a: usize) {
            if a > 0 {
                rec_pure_2(a - 1);
            }
        }

        fn rec_pure_2(a: usize) {
            if a > 0 {
                rec_pure_1(a - 1);
            }
        }

        fn main() {
            rec_pure_1(0);
        }
    }
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
    });
}

#[test]
fn mutually_recursive_impure_1() {
    inline_test! {
        fn rec_impure_1(a: usize) {
            if a > 0 {
                rec_impure_2(a - 1);
            }
            println!("{}", a);
        }

        fn rec_impure_2(a: usize) {
            if a > 0 {
                rec_impure_1(a - 1);
            }
            println!("{}", a);
        }

        fn main() {
            rec_impure_1(0);
        }
    }
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}
