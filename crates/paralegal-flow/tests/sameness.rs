#![feature(rustc_private)]

use paralegal_flow::{inline_test, test_utils::*};

#[test]
fn simple() {
    inline_test! {
        #[paralegal_flow::marker(start, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(end, arguments = [0])]
        fn target(i: usize) {}

        fn main() {
            target(source());
        }
    }
    .check_ctrl(|ctrl| {
        let sources = ctrl.marked("start");
        let target = ctrl.marked("end");
        assert!(!sources.is_empty());
        assert!(!target.is_empty());
        assert!(sources.flows_to_unchanged(&target));
    });
}

#[test]
fn no() {
    inline_test! {
        #[paralegal_flow::marker(start, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(end, arguments = [0])]
        fn target(i: usize) {}

        fn main() {
            target(source()+1);
        }
    }
    .check_ctrl(|ctrl| {
        let sources = ctrl.marked("start");
        let target = ctrl.marked("end");
        assert!(!sources.is_empty());
        assert!(!target.is_empty());
        assert!(!sources.flows_to_unchanged(&target));
    });
}

#[test]
fn through_argument() {
    inline_test! {
        #[paralegal_flow::marker(start, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(end, arguments = [0])]
        fn target(i: usize) {}

        fn wrapper(i: usize) {
            target(i)
        }

        fn main() {
            wrapper(source());
        }
    }
    .check_ctrl(|ctrl| {
        let sources = ctrl.marked("start");
        let target = ctrl.marked("end");
        assert!(!sources.is_empty());
        assert!(!target.is_empty());
        assert!(sources.flows_to_unchanged(&target));
    });
}

#[test]
fn through_return() {
    inline_test! {
        #[paralegal_flow::marker(start, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(end, arguments = [0])]
        fn target(i: usize) {}

        fn wrapper(i: usize) {
            target(i)
        }

        fn main() {
            wrapper(source());
        }
    }
    .check_ctrl(|ctrl| {
        let sources = ctrl.marked("start");
        let target = ctrl.marked("end");
        assert!(!sources.is_empty());
        assert!(!target.is_empty());
        assert!(sources.flows_to_unchanged(&target));
    });
}

#[test]
fn through_opaque_call() {
    inline_test! {
        #[paralegal_flow::marker(start, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(end, arguments = [0])]
        fn target(i: usize) {}


        fn main() {
            target(source().wrapping_add(3));
        }
    }
    .check_ctrl(|ctrl| {
        let sources = ctrl.marked("start");
        let target = ctrl.marked("end");
        assert!(!sources.is_empty());
        assert!(!target.is_empty());
        assert!(!sources.flows_to_unchanged(&target));
    });
}

#[test]
fn through_opaque_call_2() {
    inline_test! {
        #[paralegal_flow::marker(start, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(end, arguments = [0])]
        fn target(i: usize) {}

        #[paralegal_flow::marker(noinline, return)]
        fn in_between(i: usize) -> usize { i  }

        fn main() {
            target(in_between(source()));
        }
    }
    .check_ctrl(|ctrl| {
        let sources = ctrl.marked("start");
        let target = ctrl.marked("end");
        assert!(!sources.is_empty());
        assert!(!target.is_empty());
        assert!(!sources.flows_to_unchanged(&target));
    });
}

#[test]
fn in_aggregate() {
    inline_test! {
        #[paralegal_flow::marker(start, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(end, arguments = [0])]
        fn target<T>(i: T) {}

        fn main() {
            let tup = (source(), 1, 2);
            target(tup);
        }
    }
    .check_ctrl(|ctrl| {
        let sources = ctrl.marked("start");
        let target = ctrl.marked("end");
        assert!(!sources.is_empty());
        assert!(!target.is_empty());
        assert!(sources.flows_to_unchanged(&target));
    });
}

#[test]
fn not_from_projection() {
    inline_test! {
        #[paralegal_flow::marker(start, return)]
        fn source() -> (usize, usize) { (0,0) }

        #[paralegal_flow::marker(end, arguments = [0])]
        fn target<T>(i: T) {}

        fn main() {
            target(source().0);
        }
    }
    .check_ctrl(|ctrl| {
        let sources = ctrl.marked("start");
        let target = ctrl.marked("end");
        assert!(!sources.is_empty());
        assert!(!target.is_empty());
        assert!(!sources.flows_to_unchanged(&target));
    });
}
