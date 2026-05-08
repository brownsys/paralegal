#![feature(rustc_private)]

use anyhow::Result;
use helpers::Test;
use paralegal_policy::{assert_error, Context, EdgeSelection};
use paralegal_spdg::Identifier;

mod helpers;

#[test]
fn async_markers() -> Result<()> {
    let mut test = Test::new(stringify!(
        use tokio::io::AsyncWriteExt;
        use tokio::fs::File;

        type Error = Box<dyn std::error::Error + Send + Sync>;

        #[paralegal::marker(sensitive, return)]
        async fn source() -> Result<Option<&'static [u8]>, Error> {
            Ok(Some(&[]))
        }

        #[paralegal::analyze]
        async fn main() -> Result<(), Error> {
            let mut output = File::create("test").await?;

            while let Some(consumable) = source().await? {
                output.write_all(consumable).await?;
            }
            Ok(())
        }
    ))?;

    test.with_dep(["tokio", "--features", "full"]);
    test.with_external_annotations(
        "
[['tokio::io::util::async_write_ext::AsyncWriteExt::write_all']]
marker = 'sink'
on_argument = [1]
    ",
    );

    test.run(|ctx| {
        let sensitive = ctx
            .marked_nodes(Identifier::new_intern("sensitive"))
            .collect::<Vec<_>>();
        let sink = ctx
            .marked_nodes(Identifier::new_intern("sink"))
            .collect::<Vec<_>>();
        assert_error!(ctx, !sensitive.is_empty());
        assert_error!(ctx, !sink.is_empty());
        assert_error!(
            ctx,
            ctx.any_flows(&sensitive, &sink, EdgeSelection::Data)
                .is_some()
        );
        Ok(())
    })
}

#[test]
#[ignore = "https://github.com/brownsys/paralegal/issues/159"]
fn oneshot_channel() -> Result<()> {
    let mut test = Test::new(stringify!(
        #[paralegal::analyze]
        async fn main() {
            let (_, receiver) = tokio::sync::oneshot::channel();

            receiver.await.unwrap()
        }
    ))?;

    test.with_dep(["tokio", "--features", "sync"]);

    test.run(|_ctx| Ok(()))
}
