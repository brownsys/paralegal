use paralegal_flow::{inline_test, test_utils::*};

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
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn pure_call_from_static() {
    inline_test! {
        struct PureIncrementer;

        impl PureIncrementer {
            fn inc(&self, a: usize) -> usize {
                a + 1
            }
        }

        static PURE_INCREMENTER: PureIncrementer = PureIncrementer {};

        fn main(a: usize) {
            PURE_INCREMENTER.inc(a);
        }
    }
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
    });
}

#[test]
fn impure_call_from_static() {
    inline_test! {
        struct ImpureIncrementer;

        impl ImpureIncrementer {
            fn inc(&self, a: usize) -> usize {
                println!("{}", a);
                a + 1
            }
        }

        static IMPURE_INCREMENTER: ImpureIncrementer = ImpureIncrementer {};

        fn main(a: usize) {
            IMPURE_INCREMENTER.inc(a);
        }
    }
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}
