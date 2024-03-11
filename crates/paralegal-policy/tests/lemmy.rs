mod helpers;

use std::sync::Arc;

use helpers::{Result, Test};
use paralegal_policy::{assert_error, Context, EdgeSelection};
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
    assert_error!(
        ctx,
        ctx.any_flows(
            &ctx.marked_nodes(Identifier::new_intern("source"))
                .collect::<Vec<_>>(),
            &ctx.marked_nodes(Identifier::new_intern("sink"))
                .collect::<Vec<_>>(),
            EdgeSelection::Data
        )
        .is_some()
    );
    Ok(())
}

/// Tests we can handle `async_trait` version 0.1.53
#[test]
fn async_trait_1_53() -> Result<()> {
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
