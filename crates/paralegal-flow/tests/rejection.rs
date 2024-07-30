use paralegal_flow::test_utils::InlineTestBuilder;

#[test]
fn reject_closure() {
    InlineTestBuilder::new(stringify!(
        #[paralegal_flow::marker(attached, return)]
        fn attach() -> usize {
            0
        }

        fn main() {
            std::thread::spawn(|| attach());
        }
    ))
    .expect_fail_compile()
}

#[test]
fn allow_closure_simple() {
    InlineTestBuilder::new(stringify!(
        fn no_attach() -> usize {
            0
        }

        fn main() {
            std::thread::spawn(|| no_attach());
        }
    ))
    .check_ctrl(|_| ())
}

#[test]
fn reject_trait() {
    InlineTestBuilder::new(stringify!(
        #[paralegal_flow::marker(attached, return)]
        fn attach() -> usize {
            0
        }

        struct S;

        impl Clone for S {
            fn clone(&self) -> Self {
                attach();
                Self
            }
        }

        fn main() {
            Some(S).clone();
        }


    ))
    .expect_fail_compile()
}

#[test]
fn allow_trait() {
    InlineTestBuilder::new(stringify!(
        fn attach() -> usize {
            0
        }

        struct S;

        impl Clone for S {
            fn clone(&self) -> Self {
                attach();
                Self
            }
        }

        fn main() {
            Some(S).clone();
        }


    ))
    .check_ctrl(|_| ())
}
