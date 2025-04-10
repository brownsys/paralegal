#![feature(rustc_private)]

use paralegal_flow::test_utils::*;
use paralegal_spdg::Identifier;

fn marking_function_found(ctrl: CtrlRef<'_>) {
    let fns = ctrl.marked(Identifier::new_intern("source"));
    assert!(!fns.is_empty())
}

#[test]
fn marking_closure_does_not_inline() {
    InlineTestBuilder::new(stringify!(
        #[paralegal_flow::marker(source, return)]
        fn marking_function() -> usize {
            0
        }

        fn call_the_closure<R>(f: impl FnOnce() -> R) -> R {
            f()
        }

        fn main() {
            call_the_closure(|| marking_function());
        }
    ))
    .with_extra_args(["--adaptive-depth".to_string()])
    .check_ctrl(marking_function_found);
}

#[test]
fn marking_fn_ptr_does_not_inline() {
    InlineTestBuilder::new(stringify!(
        #[paralegal_flow::marker(source, return)]
        fn marking_function() -> usize {
            0
        }

        fn call_the_closure<R>(f: impl FnOnce() -> R) -> R {
            f()
        }

        fn main() {
            call_the_closure(marking_function);
        }
    ))
    .with_extra_args(["--adaptive-depth".to_string()])
    .check_ctrl(marking_function_found);
}
