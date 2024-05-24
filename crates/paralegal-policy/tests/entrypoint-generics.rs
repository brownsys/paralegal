use std::sync::Arc;

use anyhow::Result;
use helpers::Test;
use paralegal_policy::{assert_error, Context};
use paralegal_spdg::Identifier;

mod helpers;

fn simple_policy(ctx: Arc<Context>) -> Result<()> {
    let sources = ctx
        .nodes_marked_any_way(Identifier::new_intern("source"))
        .collect::<Box<_>>();
    let sinks = ctx
        .nodes_marked_any_way(Identifier::new_intern("sink"))
        .collect::<Box<_>>();
    assert_error!(ctx, !sources.is_empty());
    assert_error!(ctx, !sinks.is_empty());
    assert_error!(
        ctx,
        ctx.any_flows(&sources, &sinks, paralegal_policy::EdgeSelection::Data)
            .is_some()
    );
    Ok(())
}

#[test]
fn simple_parent() -> Result<()> {
    let test = Test::new(stringify!(
        trait Src {
            #[paralegal::marker(source, return)]
            fn source(&self) -> usize;
        }

        trait Snk {
            #[paralegal::marker(sink, arguments = [1])]
            fn sink<T>(&self, t: T);
        }

        struct Wrap<T>(T);

        impl<T: Src> Wrap<T> {
            #[paralegal::analyze]
            fn main<S: Snk>(&self, s: &S) {
                s.sink(self.0.source())
            }
        }
    ))?;

    test.run(simple_policy)
}

#[test]
fn default_method() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(source, return)]
        fn actual_source() -> usize {
            0
        }

        trait Src {
            fn source(&self) -> usize {
                actual_source()
            }
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn actual_sink<T>(t: T) {}

        trait Snk {
            fn sink(&self, t: usize) {
                actual_sink(t)
            }
        }

        struct Wrap<T>(T);

        impl<T: Src> Wrap<T> {
            #[paralegal::analyze]
            fn main<S: Snk>(&self, s: &S) {
                s.sink(self.0.source())
            }
        }
    ))?;

    test.run(simple_policy)
}

#[test]
#[ignore = "Default methods with generics don't resolve properly. See https://github.com/brownsys/paralegal/issues/152"]
fn default_method_with_generic() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(source, return)]
        fn actual_source() -> usize {
            0
        }

        trait Src {
            fn source(&self) -> usize {
                actual_source()
            }
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn actual_sink<T>(t: T) {}

        trait Snk {
            fn sink<T>(&self, t: T) {
                actual_sink(t)
            }
        }

        struct Wrap<T>(T);

        impl<T: Src> Wrap<T> {
            #[paralegal::analyze]
            fn main<S: Snk>(&self, s: &S) {
                s.sink(self.0.source())
            }
        }
    ))?;

    test.run(simple_policy)
}

#[test]
fn lifetime() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::analyze]
        async fn main<'a>() {}
    ))?;

    test.try_compile()
}

#[test]
fn object_safety() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::analyze]
        fn main<T: Clone>(t: &T) {
            let _ = t.clone();
        }
    ))?;

    test.try_compile()
}
