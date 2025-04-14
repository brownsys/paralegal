mod helpers;

use anyhow::Result;
use helpers::Test;
use paralegal_policy::{assert_error, Context, EdgeSelection};
use paralegal_spdg::Identifier;

#[test]
fn adaptive_inlines_if_reachable() -> Result<()> {
    let mut test = Test::new(stringify!(
        #[paralegal::marker(source, return)]
        fn source() -> usize {
            0
        }

        #[paralegal::marker(target, arguments=[0])]
        fn target(u: usize) {}

        fn intermediary() -> usize {
            source()
        }

        #[paralegal::analyze]
        fn main() {
            target(intermediary())
        }
    ))?;

    test.run(|ctx| {
        let sources = ctx
            .marked_nodes(Identifier::new_intern("source"))
            .collect::<Box<[_]>>();
        let targets = ctx
            .marked_nodes(Identifier::new_intern("target"))
            .collect::<Box<[_]>>();
        assert_error!(ctx, !sources.is_empty());
        assert_error!(ctx, !targets.is_empty());
        assert_error!(
            ctx,
            ctx.any_flows(&sources, &targets, EdgeSelection::Data,)
                .is_some()
        );
        Ok(())
    })
}

#[test]
fn adaptive_inlines_if_reachable_async() -> Result<()> {
    let mut test = Test::new(stringify!(
        #[paralegal::marker(source, return)]
        async fn source() -> usize {
            0
        }

        #[paralegal::marker(target, arguments=[0])]
        async fn target(u: usize) {}

        async fn intermediary() -> usize {
            source().await
        }

        #[paralegal::analyze]
        async fn main() {
            target(intermediary().await).await
        }
    ))?;

    test.run(|ctx| {
        let sources = ctx
            .marked_nodes(Identifier::new_intern("source"))
            .collect::<Box<[_]>>();
        let targets = ctx
            .marked_nodes(Identifier::new_intern("target"))
            .collect::<Box<[_]>>();
        assert_error!(ctx, !sources.is_empty());
        assert_error!(ctx, !targets.is_empty());
        assert_error!(
            ctx,
            ctx.any_flows(&sources, &targets, EdgeSelection::Data,)
                .is_some()
        );
        Ok(())
    })
}
