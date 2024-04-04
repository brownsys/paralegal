use anyhow::Result;
use helpers::Test;
use paralegal_policy::{assert_error, Context, Diagnostics, EdgeSelection, NodeQueries};
use paralegal_spdg::{GlobalNode, Identifier};
use std::sync::Arc;

mod helpers;

fn policy(ctx: Arc<Context>) -> Result<()> {
    let m_dangerous = Identifier::new_intern("dangerous");
    let m_sink = Identifier::new_intern("sink");
    let d_tys = ctx.marked_type(m_dangerous);
    assert_error!(ctx, !d_tys.is_empty());
    let ctrl = ctx.all_controllers().next().unwrap();
    for (n, ty) in ctrl.1.type_assigns.iter() {
        for d_ty in d_tys.iter() {
            if ty.0.contains(&d_ty) {
                ctx.node_note(
                    GlobalNode::from_local_node(ctrl.0, *n),
                    format!("This node has the marked type {}", ctx.describe_def(*d_ty)),
                );
            }
        }
    }
    let srcs = ctx.nodes_marked_any_way(m_dangerous).collect::<Box<_>>();
    let sinks = ctx.nodes_marked_any_way(m_sink).collect::<Box<_>>();
    assert_error!(ctx, !srcs.is_empty());
    assert_error!(ctx, !sinks.is_empty());
    for src in srcs.iter() {
        for sink in sinks.iter() {
            assert_error!(ctx, src.flows_to(*sink, &ctx, EdgeSelection::Data));
        }
    }
    Ok(())
}

#[test]
fn plain() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(dangerous)]
        struct Child {
            field: usize,
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}
        #[paralegal::marker(noinline)]
        fn source() -> Child {
            unreachable!()
        }
        #[paralegal::analyze]
        fn main() {
            let c = source();
            sink(c)
        }
    ))?;

    test.run(policy)
}

#[test]
fn plain_external() -> Result<()> {
    let mut test = Test::new(stringify!(
        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}
        #[paralegal::analyze]
        fn main() {
            sink(std::path::PathBuf::new())
        }
    ))?;
    test.with_external_annotations(
        "
[[\"std::path::PathBuf\"]]
marker = \"dangerous\"
    ",
    );
    test.run(policy)
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

    test.run(policy)
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

    test.run(policy)
}

#[test]
fn generics() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(dangerous)]
        struct Child {
            field: usize,
        }

        #[paralegal::marker(noinline)]
        fn source() -> Vec<Child> {
            unreachable!()
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let mut p = source();
            sink(p.pop());
        }
    ))?;

    test.run(policy)
}

#[test]
fn generics_fields_and_enums() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(dangerous)]
        struct Child {
            field: usize,
        }

        struct Parent {
            child: Child,
        }

        enum Parent2 {
            Child(Child),
        }

        #[paralegal::marker(noinline)]
        fn source() -> Vec<Parent> {
            unreachable!()
        }

        #[paralegal::marker(noinline)]
        fn source2() -> Vec<Parent2> {
            unreachable!()
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let mut p = source();
            sink(p.pop().unwrap().field);

            let mut p = source2();
            match p.pop() {
                Some(Parent2::Child(c)) => sink(c),
                _ => (),
            }
        }
    ))?;

    test.run(policy)
}

#[test]
fn hidden_fields() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(dangerous)]
        struct Child {
            field: usize,
        }

        struct Parent {
            child: Child,
        }

        #[paralegal::marker(noinline)]
        fn source() -> Parent {
            unreachable!()
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            sink(source());
        }
    ))?;

    test.run(policy)
}

#[test]
fn hidden_enums() -> Result<()> {
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
            sink(source())
        }
    ))?;

    test.run(policy)
}

#[test]
fn enum_precision() -> Result<()> {
    let mut test = Test::new(stringify!(
        enum Parent {
            Child(Child),
            Alternate(usize),
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
                Parent::Alternate(us) => sink(us),
                _ => (),
            }
        }
    ))?;
    test.expect_fail();
    test.run(policy)
}

#[test]
fn field_precision() -> Result<()> {
    let mut test = Test::new(stringify!(
        struct Parent {
            child: Child,
            other: usize,
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
            sink(p.other);
        }
    ))?;
    test.expect_fail();
    test.run(policy)
}
