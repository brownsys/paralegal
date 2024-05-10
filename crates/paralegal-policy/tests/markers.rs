use anyhow::Result;
use helpers::Test;
use paralegal_policy::{assert_error, Context, Diagnostics, EdgeSelection, NodeExt};
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
            if ty.0.contains(d_ty) {
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
    let mut failed = false;
    for src in srcs.iter() {
        if let Some((_, sink)) = ctx.any_flows(&[*src], &sinks, EdgeSelection::Data) {
            let mut msg = ctx.struct_node_note(
                *src,
                format!("This source flows into a sink {}", src.describe(&ctx)),
            );
            msg.with_node_note(sink, "This is the reached sink");
            msg.emit();
        } else {
            failed = true;
            ctx.node_error(
                *src,
                format!(
                    "This source does not flow into a sink: {}",
                    src.describe(&ctx)
                ),
            );
        }
    }
    if failed {
        for s in sinks.iter() {
            ctx.node_help(*s, format!("This would be a sink {}", s.describe(&ctx)));
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
        fn source() -> Option<Child> {
            unreachable!()
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let p = source();
            sink(p);
        }
    ))?;

    test.run(policy)
}

#[test]
#[ignore = "Function return values are not tracked at the level of precision of fields/variants. See https://github.com/brownsys/paralegal/issues/138"]
fn generics_precision() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(dangerous)]
        struct Child {
            field: usize,
        }

        struct V<T> {
            unrelated: usize,
            payload: Vec<T>,
        }

        #[paralegal::marker(noinline)]
        fn source() -> V<Child> {
            unreachable!()
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::marker(safe_sink, arguments = [0])]
        fn safe<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let mut p = source();
            sink(p.unrelated);
            safe(p.payload.pop())
        }
    ))?;

    test.run(|ctx| {
        let m_safe = Identifier::new_intern("safe_sink");
        let m_dangerous = Identifier::new_intern("dangerous");
        let m_sink = Identifier::new_intern("sink");
        let safe_sinks = ctx.nodes_marked_any_way(m_safe).collect::<Box<_>>();
        let dangerous = ctx.nodes_marked_any_way(m_dangerous).collect::<Box<_>>();
        let sinks = ctx.nodes_marked_any_way(m_sink).collect::<Box<_>>();
        assert_error!(ctx, !safe_sinks.is_empty());
        assert_error!(ctx, !sinks.is_empty());
        assert_error!(ctx, !dangerous.is_empty());
        if let Some((from, to)) = ctx.any_flows(&dangerous, &sinks, EdgeSelection::Data) {
            let mut msg =
                ctx.struct_node_error(from, format!("This node leaks: {}", from.describe(&ctx)));
            msg.with_node_note(to, format!("It leaks here {}", to.describe(&ctx)));
            msg.emit();
        }
        assert_error!(
            ctx,
            ctx.any_flows(&dangerous, &safe_sinks, EdgeSelection::Data)
                .is_some()
        );
        Ok(())
    })
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
        fn source() -> Option<Parent> {
            unreachable!()
        }

        #[paralegal::marker(noinline)]
        fn source2() -> Option<Parent2> {
            unreachable!()
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let mut p = source();
            sink(p.unwrap().child);

            let mut p = source2();
            match p {
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
fn hidden_generics_fields() -> Result<()> {
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
        fn source() -> Option<Vec<Parent>> {
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
fn hidden_generics_enums() -> Result<()> {
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
        fn source() -> Option<Vec<Parent2>> {
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
#[ignore = "Function return values are not tracked at the level of precision of fields/variants. See https://github.com/brownsys/paralegal/issues/138"]
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
#[ignore = "Function return values are not tracked at the level of precision of fields/variants. See https://github.com/brownsys/paralegal/issues/138"]
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

#[test]
fn references() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(dangerous)]
        struct Parent<'a> {
            child: &'a Child,
        }

        struct Child {
            field: usize,
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let c = Child { field: 0 };
            let p = Parent { child: &c };
            sink(p.child);
        }
    ))?;
    test.run(policy)
}

#[test]
fn hidden_references() -> Result<()> {
    let test = Test::new(stringify!(
        struct Parent<'a> {
            child: &'a Child,
        }

        #[paralegal::marker(dangerous)]
        struct Child {
            field: usize,
        }

        #[paralegal::marker(noinline)]
        fn source<'a>() -> Parent<'a> {
            unreachable!()
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let p = source();
            sink(p);
        }
    ))?;
    test.run(policy)
}

#[test]
fn hidden_field_and_reference() -> Result<()> {
    let test = Test::new(stringify!(
        struct Parent<'a> {
            child: &'a Child,
        }

        struct Child {
            field: Grandchild,
        }

        #[paralegal::marker(dangerous)]
        struct Grandchild {
            field: usize,
        }

        #[paralegal::marker(noinline)]
        fn source<'a>() -> Parent<'a> {
            unreachable!()
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let p = source();
            sink(p);
        }
    ))?;
    test.run(policy)
}

#[test]
#[ignore = "Undecided semantics. https://github.com/brownsys/paralegal/issues/129"]
fn mut_reference() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(dangerous)]
        struct Parent<'a> {
            child: &'a mut Child,
        }

        struct Child {
            field: usize,
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let mut c = Child { field: 0 };
            let p = Parent { child: &mut c };
            sink(c);
        }
    ))?;
    test.run(|ctx| {
        let m_dangerous = Identifier::new_intern("dangerous");
        let m_sink = Identifier::new_intern("sink");
        let srcs = ctx.nodes_marked_any_way(m_dangerous).collect::<Box<_>>();
        let sinks = ctx.nodes_marked_any_way(m_sink).collect::<Box<_>>();
        assert_error!(
            ctx,
            ctx.any_flows(&srcs, &sinks, EdgeSelection::Data).is_some()
        );
        Ok(())
    })
}

#[test]
fn field_behind_reference() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(dangerous)]
        struct Parent<'a> {
            child: &'a Child,
        }

        struct Child {
            field: std::path::PathBuf,
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let x = std::path::PathBuf::new();
            let c = Child { field: x };
            let p = Parent { child: &c };
            sink(&p.child.field);
        }
    ))?;
    test.run(policy)
}

#[test]
fn boxes() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(dangerous)]
        struct Parent {
            child: Box<Child>,
        }

        struct Child {
            field: usize,
        }

        #[paralegal::marker(sink, arguments = [0])]
        fn sink<T>(_: T) {}

        #[paralegal::analyze]
        fn main() {
            let c = Child { field: 0 };
            let p = Parent { child: Box::new(c) };
            sink(*p.child);
        }
    ))?;
    test.run(policy)
}
