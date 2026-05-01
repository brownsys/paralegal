//! These tests check that replacement models work.
//!
//! At the moment it only checks that replacing `std::thread::spawn(f)` being
//! replaced by `f()` and analogous for `tokio::spawn` works.

#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

use paralegal_flow::{define_flow_test_template, inline_test, test_utils::*};
use paralegal_spdg::Identifier;

extern crate either;
extern crate rustc_middle;

const TEST_CRATE_NAME: &str = "tests/stub-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump_and(
        TEST_CRATE_NAME,
        ["--include=crate", "--no-adaptive-approximation"]
    );
}

macro_rules! define_test {
    ($($t:tt)*) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, TEST_CRATE_NAME, $($t)*);
    };
}

const STUBS_TOML: &str = r#"
[stubs."std::thread::spawn"]
mode = "sub-closure"
generic-name = "F"

[stubs."tokio::spawn"]
mode = "sub-future"
generic-name = "F"

[stubs."actix_web::web::block"]
mode = "sub-closure"
generic-name = "F"
"#;

fn check_source_pass_target(graph: CtrlRef<'_>) {
    let src = graph.marked(Identifier::new_intern("source"));
    let pass = graph.marked(Identifier::new_intern("pass"));
    let target = graph.marked(Identifier::new_intern("target"));

    assert!(!src.is_empty());
    assert!(!pass.is_empty());
    assert!(!target.is_empty());

    assert!(src.flows_to_data(&pass));
    assert!(pass.flows_to_data(&target));
}

fn simple_source_target_flow(graph: CtrlRef<'_>) {
    let src = graph.marked(Identifier::new_intern("source"));
    let target = graph.marked(Identifier::new_intern("target"));

    assert!(!src.is_empty());
    assert!(!target.is_empty());

    assert!(src.flows_to_data(&target));
}

#[test]
fn thread_spawn() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(pass, arguments = [0])]
        fn pass<T>(t: T) -> T { t }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        fn thread_spawn() {
            let src = source();
            let next = std::thread::spawn(move || pass(src)).join().unwrap();
            target(next);
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation"])
    .with_entrypoint("crate::thread_spawn")
    .check_ctrl(check_source_pass_target)
}

#[test]
fn marked_thread_spawn() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        fn marked_thread_spawn() {
            let next = std::thread::spawn(source).join().unwrap();
            target(next);
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation"])
    .with_entrypoint("crate::marked_thread_spawn")
    .check_ctrl(simple_source_target_flow)
}

#[test]
fn marked_blocking_like() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn second_source<T>(_: T) -> usize { 0 }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        pub fn blocking_like<F, T>(pool: &str, f: F) -> T
        where
            F: FnOnce(usize) -> T + 'static + Send,
            T: 'static + Send,
        {
            let pool = pool.parse().unwrap();
            std::thread::spawn(move || (f)(pool)).join().unwrap()
        }

        fn marked_blocking_like(to_close_over: &str) {
            let next = blocking_like(to_close_over, second_source);
            target(next);
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation"])
    .with_entrypoint("crate::marked_blocking_like")
    .check_ctrl(simple_source_target_flow)
}

#[test]
fn test_blocking_like() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn second_source<T>(_: T) -> usize { 0 }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        pub fn blocking_like<F, T>(pool: &str, f: F) -> T
        where
            F: FnOnce(usize) -> T + 'static + Send,
            T: 'static + Send,
        {
            let pool = pool.parse().unwrap();
            std::thread::spawn(move || (f)(pool)).join().unwrap()
        }

        fn test_blocking_like(to_close_over: &str) {
            let next = blocking_like(to_close_over, |_| second_source(0_usize));
            target(next);
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation"])
    .with_entrypoint("crate::test_blocking_like")
    .check_ctrl(simple_source_target_flow)
}

define_test!(async_spawn: graph -> {
    check_source_pass_target(graph);
});

define_test!(marked_async_spawn: graph -> {
    simple_source_target_flow(graph);
});

define_test!(blocking_with_marker: graph -> {
    simple_source_target_flow(graph);
});

define_test!(block_fn: graph -> {
    simple_source_target_flow(graph)
});

define_test!(test_blocking_with_let_bound_closure: graph -> {
    simple_source_target_flow(graph)
});

define_test!(block_closure: graph -> {
    simple_source_target_flow(graph)
});

define_test!(strategic_overtaint: graph -> {
    simple_source_target_flow(graph)
});

define_test!(strategic_overtaint_2: graph -> {
    simple_source_target_flow(graph)
});

define_test!(no_taint_without_connection: graph -> {
    let src = graph.marked(Identifier::new_intern("source"));
    let target = graph.marked(Identifier::new_intern("target"));

    assert!(!src.is_empty());
    assert!(!target.is_empty());

    assert!(!src.flows_to_data(&target));
});
