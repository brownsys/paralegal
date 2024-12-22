//! These tests check that we only approximate functions by type signature if
//! that is sound with respect ot markers.
//!
//! Specifically if a function is parameterized by a trait and we have decided
//! to approximate it, then we check that all methods on the instantiation of
//! that trait have no reachable markers.
//!
//! It also checks that we allow approximation if no such markers are reachable.
#![feature(rustc_private)]

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

#[test]
fn reject_type() {
    InlineTestBuilder::new(stringify!(
        #[paralegal_flow::marker(target)]
        struct M;

        struct Iter;

        impl Iterator for Iter {
            type Item = M;

            fn next(&mut self) -> Option<M> { None }
        }

        fn main() {
            [M].into_iter().chain(Iter);
        }
    ))
    .expect_fail_compile()
}
