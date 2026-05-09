#![feature(rustc_private)]

use paralegal_flow::{inline_test, test_utils::*};
use paralegal_pdg::Identifier;

const EXTRA_ARGS: [&str; 2] = ["--include=crate", "--no-adaptive-approximation"];

#[test]
fn simple_overtaint() {
    inline_test! {
        type F = usize;

        #[paralegal_flow::marker(source, return)]
        fn source() -> Box<F> { unreachable!() }

        #[paralegal_flow::marker(checkpoint, return)]
        fn checkpoint<T>(_: T) -> Box<F> { unreachable!() }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        fn main() {
            sink(checkpoint(source()))
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let sources = graph.marked(Identifier::new_intern("source"));
        let mid = graph.marked(Identifier::new_intern("checkpoint"));
        let end = graph.marked(Identifier::new_intern("sink"));
        assert!(!sources.is_empty());
        assert!(!mid.is_empty());
        assert!(!end.is_empty());
        assert!(sources.always_happens_before_data(&mid, &end));
    });
}

#[test]
fn ref_with_checkpoint() {
    inline_test! {
        type F = usize;

        #[paralegal_flow::marker(source, return)]
        fn source() -> Box<F> { unreachable!() }

        #[paralegal_flow::marker(checkpoint_2, return)]
        fn checkpoint_2<T>(i: T) -> Box<T> { Box::new(i) }

        #[paralegal_flow::marker(modifier, return)]
        fn modifier() -> usize { 6 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        fn main() {
            let mut inp = source();
            let r = checkpoint_2(&mut inp);
            ***r += modifier();
            sink(inp);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let sources = graph.marked(Identifier::new_intern("source"));
        let mid = graph.marked(Identifier::new_intern("checkpoint_2"));
        let end = graph.marked(Identifier::new_intern("sink"));
        let modifier = graph.marked(Identifier::new_intern("modifier"));
        assert!(!sources.is_empty());
        assert!(!mid.is_empty());
        assert!(!end.is_empty());
        assert!(!modifier.is_empty());
        assert!(modifier.flows_to_data(&end));
        assert!(sources.flows_to_data(&end));
        assert!(!mid.always_happens_before_data(&modifier, &end));
    });
}

#[test]
fn field_ref() {
    inline_test! {
        #[paralegal_flow::marker(source_2, return)]
        fn source_2() -> usize { 0 }

        #[paralegal_flow::marker(modifier, return)]
        fn modifier() -> usize { 6 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        fn main() {
            let mut inp = (source_2(),);
            let my_ref = &mut inp;
            my_ref.0 += modifier();
            sink(inp);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let sources = graph.marked(Identifier::new_intern("source_2"));
        let end = graph.marked(Identifier::new_intern("sink"));
        let modifier = graph.marked(Identifier::new_intern("modifier"));
        assert!(!sources.is_empty());
        assert!(!end.is_empty());
        assert!(!modifier.is_empty());
        assert!(modifier.flows_to_data(&end));
        assert!(sources.flows_to_data(&end));
        assert!(!sources.always_happens_before_data(&modifier, &end));
    });
}

#[test]
fn ref_mut_box() {
    inline_test! {
        #[paralegal_flow::marker(source_2, return)]
        fn source_2() -> usize { 0 }

        #[paralegal_flow::marker(modifier, return)]
        fn modifier() -> usize { 6 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        fn main() {
            let mut inp = Box::new(source_2());
            let my_ref = &mut inp;
            **my_ref += modifier();
            sink(inp);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let sources = graph.marked(Identifier::new_intern("source_2"));
        let end = graph.marked(Identifier::new_intern("sink"));
        let modifier = graph.marked(Identifier::new_intern("modifier"));
        assert!(!sources.is_empty());
        assert!(!end.is_empty());
        assert!(!modifier.is_empty());
        assert!(modifier.flows_to_data(&end));
        assert!(sources.flows_to_data(&end));
        assert!(!sources.always_happens_before_data(&modifier, &end));
    });
}

#[test]
fn box_ref_mut() {
    inline_test! {
        #[paralegal_flow::marker(source_2, return)]
        fn source_2() -> usize { 0 }

        #[paralegal_flow::marker(modifier, return)]
        fn modifier() -> usize { 6 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        fn main() {
            let mut src = source_2();
            let mut inp = Box::new(&mut src);
            **inp += modifier();
            sink(src);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let sources = graph.marked(Identifier::new_intern("source_2"));
        let end = graph.marked(Identifier::new_intern("sink"));
        let modifier = graph.marked(Identifier::new_intern("modifier"));
        assert!(!sources.is_empty());
        assert!(!end.is_empty());
        assert!(!modifier.is_empty());
        assert!(modifier.flows_to_data(&end));
        assert!(sources.flows_to_data(&end));
        assert!(!sources.always_happens_before_data(&modifier, &end));
    });
}

#[test]
#[ignore = "Box modification is not currently considered strong. \
    See https://github.com/brownsys/paralegal/issues/155"]
fn strong_box_update() {
    inline_test! {
        #[paralegal_flow::marker(source_2, return)]
        fn source_2() -> usize { 0 }

        #[paralegal_flow::marker(modifier, return)]
        fn modifier() -> usize { 6 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        fn main() {
            let mut inp = Box::new(source_2());
            let r = &mut inp;
            **r = modifier();
            sink(inp);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let sources = graph.marked(Identifier::new_intern("source_2"));
        let end = graph.marked(Identifier::new_intern("sink"));
        let modifier = graph.marked(Identifier::new_intern("modifier"));
        assert!(!sources.is_empty());
        assert!(!end.is_empty());
        assert!(!modifier.is_empty());
        assert!(modifier.flows_to_data(&end));
        assert!(!sources.flows_to_data(&end));
    });
}

#[test]
fn strong_ref_in_box_update() {
    inline_test! {
        #[paralegal_flow::marker(source_2, return)]
        fn source_2() -> usize { 0 }

        #[paralegal_flow::marker(modifier, return)]
        fn modifier() -> usize { 6 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        fn main() {
            let mut src = source_2();
            let mut inp = Box::new(&mut src);
            **inp = modifier();
            sink(src);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let sources = graph.marked(Identifier::new_intern("source_2"));
        let end = graph.marked(Identifier::new_intern("sink"));
        let modifier = graph.marked(Identifier::new_intern("modifier"));
        assert!(!sources.is_empty());
        assert!(!end.is_empty());
        assert!(!modifier.is_empty());
        assert!(modifier.flows_to_data(&end));
        assert!(!sources.flows_to_data(&end));
    });
}

// The next two tests exercise alias analysis through NonNull<T>, whose inner
// pointer field is a pattern type (`*const T is !null`) in recent toolchains.
// RegionVisitor must traverse the Pat layer via OpaqueCast to reach the raw
// pointer and Deref it, or it would either panic or miss the alias entirely.

#[test]
fn nonnull_read() {
    inline_test! {
        use std::ptr::NonNull;

        #[paralegal_flow::marker(source_2, return)]
        fn source_2() -> usize { 0 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        fn main() {
            let src = source_2();
            let nn = unsafe { NonNull::new_unchecked(&src as *const usize as *mut usize) };
            let val = unsafe { nn.read() };
            sink(val);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let sources = graph.marked(Identifier::new_intern("source_2"));
        let end = graph.marked(Identifier::new_intern("sink"));
        assert!(!sources.is_empty());
        assert!(!end.is_empty());
        assert!(sources.flows_to_data(&end));
    });
}

#[test]
fn nonnull_write() {
    inline_test! {
        use std::ptr::NonNull;

        #[paralegal_flow::marker(source_2, return)]
        fn source_2() -> usize { 0 }

        #[paralegal_flow::marker(modifier, return)]
        fn modifier() -> usize { 6 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        fn main() {
            let mut src = source_2();
            let nn = unsafe { NonNull::new_unchecked(&mut src as *mut usize) };
            unsafe { *nn.as_ptr() += modifier() };
            sink(src);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let sources = graph.marked(Identifier::new_intern("source_2"));
        let end = graph.marked(Identifier::new_intern("sink"));
        let modifier = graph.marked(Identifier::new_intern("modifier"));
        assert!(!sources.is_empty());
        assert!(!end.is_empty());
        assert!(!modifier.is_empty());
        // `*= ` reads the old value of src, so source_2 is always part of what flows
        // to sink regardless of whether the write-back alias is tracked.
        assert!(sources.flows_to_data(&end));
    });
}
