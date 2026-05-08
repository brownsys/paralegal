#![feature(rustc_private)]

use flowistry_pdg::Constant;
use paralegal_flow::test_utils::FlowsTo;

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
