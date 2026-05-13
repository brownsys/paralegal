#![feature(rustc_private)]

use paralegal_flow::test_utils::{FlowsTo, InlineTestBuilder};
use paralegal_pdg::Constant;

use paralegal_flow::inline_test;

#[test]
fn discovery() {
    inline_test! {
        fn main() {
            if true {
                let x = 42;
            } else {
                let s = "find me".to_string();
            }
        }
    }
    .check_ctrl(|ctrl| {
        let consts = ctrl.constants().collect::<Vec<_>>();

        dbg!(&consts);

        for c in [
            Constant::string("find me"),
            Constant::bool(true),
            Constant::int(42),
            Constant::zst("()"),
        ] {
            assert!(
                consts.iter().any(|(_, constant)| constant == &c),
                "Could not find constant `{c}`"
            );
        }
    })
}

#[test]
fn multiple_same() {
    inline_test! {
        fn main() {
            let x = "find me";
            let y = "find me";
        }
    }
    .check_ctrl(|ctrl| {
        let consts = ctrl.constants().collect::<Vec<_>>();

        dbg!(&consts);

        assert_eq!(
            consts
                .iter()
                .filter(|(_, constant)| constant == &Constant::string("find me"))
                .count(),
            2,
            "Could not find constants"
        );
    })
}

#[test]
fn multiple_constants_in_call() {
    inline_test! {
        fn main() {
            let _ = std::ops::BitOr::bitor(false, false);
        }
    }
    .check_ctrl(|ctrl| {
        let consts = ctrl.constants().collect::<Vec<_>>();

        dbg!(&consts);

        assert_eq!(
            consts
                .iter()
                .filter(|(_, constant)| constant == &Constant::bool(false))
                .count(),
            2,
            "Could not find constant"
        );
    })
}

#[test]
fn flow() {
    inline_test! {
        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(_: i32) {}

        fn main() {
            target(42);
        }
    }
    .check_ctrl(|ctrl| {
        let c = ctrl.get_constant(Constant::int(42));
        let targets = ctrl.marked("target");
        assert!(!targets.is_empty());
        if let Some(c) = c {
            assert!(c.flows_to_data(&targets));
        } else {
            panic!("Could not find constant");
        }
    });
}

#[test]
fn flow_with_intermediate() {
    inline_test! {
        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(_: i32) {}

        fn main() {
            target(42 + 1);
        }
    }
    .check_ctrl(|ctrl| {
        let c = ctrl.get_constant(Constant::int(42));
        let targets = ctrl.marked("target");
        assert!(!targets.is_empty());
        if let Some(c) = c {
            assert!(c.flows_to_data(&targets));
        } else {
            panic!("Could not find constant");
        }
    });
}

// Regression: the fallback in `ConstConversionError::handle_default_policy`
// (in `crates/plugin/src/constants.rs`) used to call
// `tcx.dcx().span_err(span, ...)` directly instead of going through the
// strict-respecting `emit` closure. Default-mode analysis (no `--strict`)
// hard-errored on any unsupported constant reaching the fallback —
// `Integer128NotSupported`, `EvalFailed`, and any `Val` payload that the
// per-type match didn't recognize (the `_ => ()` arm at the bottom of
// `UnsupportedConstType`'s inner match).
//
// We exercise both fallback shapes: f64 reaches the catch-all via the
// `UnsupportedConstType(Val(..))` arm; u128 skips the outer if-let
// entirely (`Integer128NotSupported`) and lands directly in the catch-all.
#[test]
fn unsupported_float_literal_silent_under_default() {
    inline_test! {
        fn sink(_: f64) {}
        fn main() {
            sink(3.14_f64);
        }
    }
    .check_ctrl(|_| {});
}

#[test]
fn unsupported_u128_literal_silent_under_default() {
    inline_test! {
        fn sink(_: u128) {}
        fn main() {
            sink(1_u128);
        }
    }
    .check_ctrl(|_| {});
}

// Complementary negative test: `--strict` must still produce an error on
// the fallback path. Pins the post-fix behavior so a future refactor that
// overcorrects (e.g. routes everything through `emit` *and* removes the
// `strict` gate) would be caught here.
#[test]
fn unsupported_float_literal_errors_under_strict() {
    InlineTestBuilder::new(stringify!(
        fn sink(_: f64) {}
        fn main() {
            sink(3.14_f64);
        }
    ))
    .with_extra_args(["--strict".to_string()])
    .expect_fail_compile();
}
