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

#[test]
fn test_mutable_references() {
    // This doesn't actually test any functionality but is an experiment to see
    // whether the PDG accurately shows an absence of a flow if a coerced
    // reference is used as though it has local lifetime.
    //
    // When a simple stack variable like this is used the PDG correctly shows
    // the absence of a flow. However using a `Vec` instead (see next test case)
    // already introduces the flow.
    //
    // Note that we aren't analyzing the stdlib here, but even if we did, we add
    // exception markers to vectors, so the outcome is likely the same.

    inline_test! {
        use std::cell::RefCell;

        #[paralegal_flow::marker(source, return)]
        fn mark<T>(t: T) -> T{
            t
        }

        struct S;

        fn with(mut f: impl for<'a> FnMut(&'a mut S)) {
            let r = unsafe { std::mem::transmute(&mut SC) };
            f(r)
        }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn on_s(s: &mut S) {}

        const SC: S = S;

        fn main() {
            let mutex : RefCell<&'static mut S> = RefCell::new(unsafe { std::mem::transmute(&mut SC) });
            with(|s| {
                let s = mark(s);
                let mut guard = mutex.borrow_mut();
                let mut my_s = s;
                my_s = *guard;
                on_s(my_s);
            })
        }
    }.check_ctrl(|ctrl| {
        let sources = ctrl.marked("source");
        let targets = ctrl.marked("target");
        assert!(!sources.is_empty());
        assert!(!targets.is_empty());
        assert!(!sources.flows_to_data(&targets));
    });
}

#[test]
fn test_mutable_references_2() {
    // See comments on `test_mutable_references`

    inline_test! {
        use std::cell::RefCell;

        #[paralegal_flow::marker(source, return)]
        fn mark<T>(t: T) -> T{
            t
        }

        struct S;

        fn with(mut f: impl for<'a> FnMut(&'a mut S)) {
            let r = unsafe { std::mem::transmute(&mut SC) };
            f(r)
        }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn on_s(s: &mut S) {}

        const SC: S = S;

        fn main() {
            let mutex : RefCell<&'static mut S> = RefCell::new(unsafe { std::mem::transmute(&mut SC) });
            with(|s| {
                let s = mark(s);
                let mut v = vec![s];
                let mut guard = mutex.borrow_mut();
                v.pop();
                v.push(*guard);
                on_s(v.pop().unwrap());
            })
        }
    }.check_ctrl(|ctrl| {
        let sources = ctrl.marked("source");
        let targets = ctrl.marked("target");
        assert!(!sources.is_empty());
        assert!(!targets.is_empty());
        assert!(sources.flows_to_data(&targets));
    });
}
