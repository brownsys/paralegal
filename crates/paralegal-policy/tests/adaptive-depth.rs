#![feature(rustc_private)]

use anyhow::Result;
use helpers::Test;
use paralegal_policy::{assert_error, Context, EdgeSelection};
use paralegal_spdg::Identifier;

mod helpers;

#[test]
fn higher_order_futures() -> Result<()> {
    let test = Test::new(stringify!(
        use std::future;
        use std::time;
        #[paralegal::marker(source, return)]
        fn source() -> usize {
            0
        }

        pub async fn add_card_to_locker() -> usize {
            record_operation_time(async { source() }).await
        }
        pub async fn record_operation_time<F, R>(future: F) -> R
        where
            F: future::Future<Output = R>,
        {
            let (result, _) = time_future(future).await;
            result
        }

        pub async fn time_future<F, R>(future: F) -> (R, time::Duration)
        where
            F: future::Future<Output = R>,
        {
            let start = time::Instant::now();
            let result = future.await;
            let time_spent = start.elapsed();
            (result, time_spent)
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(t: T) {}

        #[paralegal::analyze]
        async fn main() {
            sink(add_card_to_locker().await)
        }
    ))?;

    test.run(|ctx| {
        let m_source = Identifier::new_intern("source");
        let m_sink = Identifier::new_intern("sink");
        let sources = ctx.nodes_marked_any_way(m_source).collect::<Box<_>>();
        let sinks = ctx.nodes_marked_any_way(m_sink).collect::<Box<_>>();
        assert_error!(ctx, !sources.is_empty());
        assert_error!(ctx, !sinks.is_empty());
        assert_error!(
            ctx,
            ctx.any_flows(&sources, &sinks, EdgeSelection::Data)
                .is_some()
        );
        Ok(())
    })
}
