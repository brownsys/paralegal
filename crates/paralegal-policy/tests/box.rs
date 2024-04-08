use anyhow::Result;
use helpers::Test;
use paralegal_policy::{algo::ahb, assert_error};
use paralegal_spdg::{HashSet, Identifier};

mod helpers;

#[test]
fn much_simpler_box_test_case() -> Result<()> {
    let mut test = Test::new(stringify!(
        type F = usize;
        #[paralegal::marker(source, return)]
        fn source() -> Box<F> {
            unreachable!()
        }

        #[paralegal::marker(checkpoint, return)]
        fn checkpoint<T>(_: T) -> Box<F> {
            unreachable!()
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            sink(checkpoint(source()))
        }
    ))?;

    test.context_config().always_happens_before_tracing = ahb::TraceLevel::Full;

    test.run(|ctx| {
        let sources = ctx
            .nodes_marked_any_way(Identifier::new_intern("source"))
            .collect::<Box<_>>();
        let checkpoints = ctx
            .nodes_marked_any_way(Identifier::new_intern("checkpoint"))
            .collect::<HashSet<_>>();
        let sinks = ctx
            .nodes_marked_any_way(Identifier::new_intern("sink"))
            .collect::<HashSet<_>>();
        assert_error!(ctx, !sinks.is_empty());
        assert_error!(ctx, !checkpoints.is_empty());
        assert_error!(ctx, !sources.is_empty());
        ctx.always_happens_before(
            sources.iter().copied(),
            |a| checkpoints.contains(&a),
            |t| sinks.contains(&t),
        )?
        .report(ctx.clone());
        Ok(())
    })
}
