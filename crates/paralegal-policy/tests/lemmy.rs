mod helpers;

use std::sync::Arc;

use helpers::{Result, Test};
use paralegal_policy::{assert_error, assert_warning, Context, Diagnostics, EdgeSelection};
use paralegal_spdg::Identifier;

const ASYNC_TRAIT_CODE: &str = stringify!(
    pub struct SaveComment {
        pub save: bool,
    }
    #[async_trait::async_trait(?Send)]
    pub trait Perform {
        type Response;

        async fn perform(&self) -> Result<Self::Response, String>;
    }

    #[async_trait::async_trait(?Send)]
    impl Perform for SaveComment {
        type Response = ();
        #[paralegal::analyze]
        async fn perform(&self) -> Result<(), String> {
            save(create().await).await;
            Ok(())
        }
    }

    #[paralegal::marker(source, return)]
    async fn create() -> usize {
        0
    }

    #[paralegal::marker(sink, arguments = [0])]
    async fn save(u: usize) {}
);

fn async_trait_policy(ctx: Arc<Context>) -> Result<()> {
    let sinks = ctx
        .marked_nodes(Identifier::new_intern("sink"))
        .collect::<Vec<_>>();
    for s in &sinks {
        ctx.node_note(*s, "Found this match for the sink marker");
    }
    assert_warning!(ctx, !sinks.is_empty(), "No sinks found");
    assert_error!(
        ctx,
        ctx.any_flows(
            &ctx.marked_nodes(Identifier::new_intern("source"))
                .collect::<Vec<_>>(),
            &sinks,
            EdgeSelection::Data
        )
        .is_some()
    );
    Ok(())
}

/// Tests we can handle `async_trait` version 0.1.53
#[test]
fn async_trait_0_1_53() -> Result<()> {
    let mut test = Test::new(ASYNC_TRAIT_CODE)?;
    test.with_dep(["async-trait@=0.1.53"]);
    test.run(async_trait_policy)
}

/// Tests we can handle whichever latest `async_trait` version cargo pulls for
/// us
#[test]
fn async_trait_latest() -> Result<()> {
    let mut test = Test::new(ASYNC_TRAIT_CODE)?;
    test.with_dep(["async-trait"]);
    test.run(async_trait_policy)
}

const CALLING_ASYNC_TRAIT_CODE: &str = stringify!(
    struct Ctx(usize, bool);

    #[paralegal::marker(source, return)]
    async fn source(_context: &Ctx) -> usize {
        0
    }

    #[paralegal::marker(sink, arguments = [0])]
    fn sink<T>(sink: T) {}

    #[paralegal::analyze]
    async fn main() {
        sink(Ctx(8, true).foo().await.unwrap())
    }

    #[async_trait::async_trait(?Send)]
    trait AsyncTrait {
        async fn foo(&self) -> Result<usize, String>;
    }

    #[async_trait::async_trait(?Send)]
    impl AsyncTrait for Ctx {
        async fn foo(&self) -> Result<usize, String> {
            Ok(source(self).await + self.0)
        }
    }
);

fn calling_async_trait_policy(ctx: Arc<Context>) -> Result<()> {
    let sources = Vec::from_iter(ctx.marked_nodes(Identifier::new_intern("source")));
    let sinks = Vec::from_iter(ctx.marked_nodes(Identifier::new_intern("sink")));
    assert_error!(ctx, !sources.is_empty());
    assert_error!(ctx, !sinks.is_empty());
    assert_error!(
        ctx,
        ctx.any_flows(&sources, &sinks, EdgeSelection::Data)
            .is_some()
    );
    Ok(())
}

/// Turns out flowistry can actually handle calling async functions from
/// `async_trait` as well. So here we test that that works.
#[test]
fn support_calling_async_trait_0_1_53() -> Result<()> {
    let mut test = Test::new(CALLING_ASYNC_TRAIT_CODE)?;
    test.with_dep(["async-trait@=0.1.53"]);
    test.run(calling_async_trait_policy)
}
