//! These tests check that replacement models work.
//!
//! At the moment it only checks that replacing `std::thread::spawn(f)` being
//! replaced by `f()` and analogous for `tokio::spawn` works.

#![feature(rustc_private)]

use paralegal_flow::{inline_test, test_utils::*};
use paralegal_spdg::Identifier;
use std::sync::OnceLock;

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

/// Dependency environment configured with external crates (tokio, actix_web, etc.)
/// This is built once and reused across all tests in this file.
static DEPENDENCY_ENV: OnceLock<DependencyEnvironment> = OnceLock::new();

fn dependency_environment() -> &'static DependencyEnvironment {
    DEPENDENCY_ENV.get_or_init(|| {
        DependencyEnvironmentBuilder::new()
            .with_manifest(
                std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                    .join("tests/stub-tests/Cargo.toml"),
            )
            .build()
    })
}

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
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
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
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
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
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
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
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
    .with_entrypoint("crate::test_blocking_like")
    .check_ctrl(simple_source_target_flow)
}

#[test]
fn async_spawn() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(pass, arguments = [0])]
        fn pass<T>(t: T) -> T { t }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        async fn async_spawn() {
            let src = source();
            let next = tokio::spawn(async move { pass(src) }).await.unwrap();
            target(next);
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
    .with_entrypoint("crate::async_spawn")
    .check_ctrl(check_source_pass_target)
}

#[test]
fn marked_async_spawn() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        async fn async_source() -> usize { 0 }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        async fn marked_async_spawn() {
            let next = tokio::spawn(async_source()).await.unwrap();
            target(next);
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
    .with_entrypoint("crate::marked_async_spawn")
    .check_ctrl(simple_source_target_flow)
}

#[test]
fn block_fn() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        fn to_block() -> Result<usize, actix_web::error::BlockingError> {
            Ok(source())
        }

        async fn block_fn() -> Result<(), actix_web::error::BlockingError> {
            Ok(target(actix_web::web::block(to_block).await?? + 1))
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
    .with_entrypoint("crate::block_fn")
    .check_ctrl(simple_source_target_flow)
}

#[test]
fn block_closure() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        async fn block_closure(to_close_over: usize) -> Result<(), actix_web::error::BlockingError> {
            Ok(target(
                actix_web::web::block(move || Ok(source() + to_close_over)).await?? + 1,
            ))
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
    .with_entrypoint("crate::block_closure")
    .check_ctrl(simple_source_target_flow)
}

#[test]
fn blocking_with_marker() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn second_source<T>(_: T) -> usize { 0 }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        pub async fn blocking<F, T>(pool: &str, f: F) -> T
        where
            F: FnOnce(usize) -> T + 'static + Send,
            T: 'static + Send,
        {
            let pool = pool.parse().unwrap();
            actix_web::web::block(move || (f)(pool)).await.unwrap()
        }

        async fn blocking_with_marker(to_close_over: &str) {
            target(blocking(to_close_over, second_source).await)
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
    .with_entrypoint("crate::blocking_with_marker")
    .check_ctrl(simple_source_target_flow)
}

#[test]
fn test_blocking_with_let_bound_closure() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        pub async fn blocking<F, T>(pool: &str, f: F) -> T
        where
            F: FnOnce(usize) -> T + 'static + Send,
            T: 'static + Send,
        {
            let pool = pool.parse().unwrap();
            actix_web::web::block(move || (f)(pool)).await.unwrap()
        }

        async fn test_blocking_with_let_bound_closure(to_close_over: &str) {
            let from_scope = 10;
            let the_closure = move |u| u + source() + from_scope;
            target(blocking(to_close_over, the_closure).await);
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
    .with_entrypoint("crate::test_blocking_with_let_bound_closure")
    .check_ctrl(simple_source_target_flow)
}

#[test]
fn strategic_overtaint() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        async fn strategic_overtaint(to_close_over: usize) -> Result<(), actix_web::error::BlockingError> {
            Ok(target(
                actix_web::web::block(move || Ok((source(), to_close_over)))
                    .await??
                    .0,
            ))
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
    .with_entrypoint("crate::strategic_overtaint")
    .check_ctrl(simple_source_target_flow)
}

#[test]
fn strategic_overtaint_2() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        async fn strategic_overtaint_2(to_close_over: usize) -> Result<(), actix_web::error::BlockingError> {
            Ok(target(
                actix_web::web::block(move || Ok((source(), to_close_over)))
                    .await??
                    .1,
            ))
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
    .with_entrypoint("crate::strategic_overtaint_2")
    .check_ctrl(simple_source_target_flow)
}

#[test]
fn no_taint_without_connection() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn source() -> usize { 0 }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn target(i: usize) {}

        async fn no_taint_without_connection(to_close_over: usize) -> Result<(), actix_web::error::BlockingError> {
            Ok(target(
                actix_web::web::block(move || {
                    let _no_use = source();
                    Ok(to_close_over)
                })
                .await??,
            ))
        }
    }
    .with_build_config(STUBS_TOML)
    .with_extra_args(["--no-adaptive-approximation", "--include=crate"])
    .with_dependency_environment(dependency_environment())
    .with_entrypoint("crate::no_taint_without_connection")
    .check_ctrl(|graph| {
        let src = graph.marked(Identifier::new_intern("source"));
        let target = graph.marked(Identifier::new_intern("target"));

        assert!(!src.is_empty());
        assert!(!target.is_empty());

        assert!(!src.flows_to_data(&target));
    })
}
