use anyhow::Result;
use helpers::Test;
use paralegal_policy::assert_error;
use paralegal_spdg::Identifier;

mod helpers;

#[test]
fn plain() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(dangerous)]
        struct Child {
            field: usize,
        }

        #[paralegal::marker(noinline)]
        fn source() -> Child {
            unreachable!()
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let c = source();
            sink(c)
        }
    ))?;

    test.run(|ctx| {
        let srcs = ctx
            .nodes_marked_any_way(Identifier::new_intern("dangerous"))
            .collect::<Box<_>>();
        let sinks = ctx
            .nodes_marked_any_way(Identifier::new_intern("sink"))
            .collect::<Box<_>>();
        assert_error!(ctx, !srcs.is_empty());
        assert_error!(ctx, !sinks.is_empty());
        assert_error!(
            ctx,
            ctx.any_flows(&srcs, &sinks, paralegal_policy::EdgeSelection::Data)
                .is_some()
        );
        Ok(())
    })
}

#[test]
fn enums() -> Result<()> {
    let test = Test::new(stringify!(
        enum Parent {
            Child(Child),
        }

        #[paralegal::marker(dangerous)]
        struct Child {
            field: usize,
        }

        #[paralegal::marker(noinline)]
        fn source() -> Parent {
            unreachable!()
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            match source() {
                Parent::Child(c) => sink(c),
            }
        }
    ))?;

    test.run(|ctx| {
        let srcs = ctx
            .nodes_marked_any_way(Identifier::new_intern("dangerous"))
            .collect::<Box<_>>();
        let sinks = ctx
            .nodes_marked_any_way(Identifier::new_intern("sink"))
            .collect::<Box<_>>();
        assert_error!(ctx, !srcs.is_empty());
        assert_error!(ctx, !sinks.is_empty());
        assert_error!(
            ctx,
            ctx.any_flows(&srcs, &sinks, paralegal_policy::EdgeSelection::Data)
                .is_some()
        );
        Ok(())
    })
}

#[test]
fn fields() -> Result<()> {
    let test = Test::new(stringify!(
        struct Parent {
            child: Child,
        }

        #[paralegal::marker(dangerous)]
        struct Child {
            field: usize,
        }

        #[paralegal::marker(noinline)]
        fn source() -> Parent {
            unreachable!()
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let p = source();
            sink(p.child);
        }
    ))?;

    test.run(|ctx| {
        let srcs = ctx
            .nodes_marked_any_way(Identifier::new_intern("dangerous"))
            .collect::<Box<_>>();
        let sinks = ctx
            .nodes_marked_any_way(Identifier::new_intern("sink"))
            .collect::<Box<_>>();
        assert_error!(ctx, !srcs.is_empty());
        assert_error!(ctx, !sinks.is_empty());
        assert_error!(
            ctx,
            ctx.any_flows(&srcs, &sinks, paralegal_policy::EdgeSelection::Data)
                .is_some()
        );
        Ok(())
    })
}
