mod helpers;

use anyhow::Result;
use helpers::Test;
use paralegal_policy::{assert_error, Diagnostics, EdgeSelection};
use paralegal_spdg::Identifier;

#[test]
fn return_markers_on_no_arg_functions() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(target, arguments = [0])]
        fn target<T>(t: T) {}

        #[paralegal::marker(source, return)]
        fn source() -> std::path::PathBuf {
            "buf".into()
        }

        #[paralegal::analyze]
        fn main() {
            let x = source();
            target(x)
        }
    ))?;

    test.run(|ctx| {
        let sources: Box<[_]> = ctx.marked_nodes(Identifier::new_intern("source")).collect();
        let targets: Box<[_]> = ctx.marked_nodes(Identifier::new_intern("target")).collect();
        assert_error!(ctx, !sources.is_empty(), "No sources");
        assert_error!(ctx, !targets.is_empty(), "No targets");
        assert_error!(
            ctx,
            ctx.any_flows(&sources, &targets, EdgeSelection::Data)
                .is_some()
        );
        Ok(())
    })
}

#[test]
fn flows_to_self() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(self, arguments = [0])]
        fn foo(arg: usize) {}

        #[paralegal::marker(noinline)]
        fn non_const() -> usize {
            unimplemented!()
        }

        #[paralegal::analyze]
        fn main() {
            let x = non_const();
            let _ = foo(x);
        }

        #[paralegal::marker(source, return)]
        fn source() -> usize {
            9
        }

        #[paralegal::marker(target, arguments = [0])]
        fn target(t: usize) {}

        #[paralegal::analyze]
        fn main2() {
            target(source())
        }
    ))?;

    test.run(|ctx| {
        let marked_self = ctx
            .marked_nodes(Identifier::new_intern("self"))
            .collect::<Box<[_]>>();

        assert_error!(ctx, !marked_self.is_empty());

        assert_error!(
            ctx,
            ctx.any_flows(&marked_self, &marked_self, EdgeSelection::Data)
                .is_some()
        );
        // QUESTION: Should this also hold for control flow??

        let marked_source = ctx
            .marked_nodes(Identifier::new_intern("source"))
            .collect::<Box<[_]>>();
        let marked_target = ctx
            .marked_nodes(Identifier::new_intern("target"))
            .collect::<Box<[_]>>();

        assert_error!(ctx, !marked_source.is_empty());
        assert_error!(ctx, !marked_target.is_empty());

        assert_error!(
            ctx,
            ctx.any_flows(&marked_source, &marked_target, EdgeSelection::Data)
                .is_some()
        );

        Ok(())
    })
}

#[test]
fn simple_monomorphization() -> Result<()> {
    let test = Test::new(stringify!(
        struct Donator;
        struct Receiver;

        trait Tr {
            fn source(&self) -> usize;
            fn target<T>(&self, t: T);
        }

        impl Tr for Donator {
            #[paralegal::marker(source, return)]
            fn source(&self) -> usize { 0 }
            fn target<T>(&self, t: T) {}
        }

        impl Tr for Receiver {
            fn source(&self) -> usize { 0 }
            #[paralegal::marker(target, arguments = [1])]
            fn target<T>(&self, t: T) {}
        }

        #[paralegal::analyze]
        fn connected() {
            Receiver.target(Donator.source())
        }

        #[paralegal::analyze]
        fn unconnected() {
            Receiver.target(Donator.source())
        }
    ))?;
    test.run(|ctx| {
        ctx.controller_contexts().for_each(|ctx| {
            let sources: Box<[_]> = ctx
                .marked_nodes(Identifier::new_intern("source"))
                .filter(|n| n.controller_id() == ctx.id())
                .collect();
            let targets: Box<[_]> = ctx
                .marked_nodes(Identifier::new_intern("target"))
                .filter(|n| n.controller_id() == ctx.id())
                .collect();

            let expect_connect = ctx.current().name.as_str() != "connected";

            assert_error!(
                ctx,
                !expect_connect || !sources.is_empty(),
                "Source presence. Expectation: {}",
                expect_connect
            );
            assert_error!(
                ctx,
                !expect_connect || !targets.is_empty(),
                "Target presence. Expectation: {}",
                expect_connect
            );
            assert_error!(
                ctx,
                !expect_connect
                    || ctx
                        .any_flows(&sources, &targets, EdgeSelection::Data)
                        .is_some(),
                "Flow. Expectation: {}",
                expect_connect
            );
            for &src in sources.iter() {
                ctx.node_note(src, format!("This is a source {}", ctx.describe_node(src)));
            }
            for &src in targets.iter() {
                ctx.node_note(src, format!("This is a target {}", ctx.describe_node(src)));
            }
        });
        Ok(())
    })
}

#[test]
#[ignore = "Marker assignment in generic functions that need monomorphization are broken."]
fn markers_on_generic_calls() -> Result<()> {
    let test = Test::new(stringify!(
        struct Donator;
        struct Receiver;

        trait Tr {
            fn source(&self) -> usize;
            fn target<T>(&self, t: T);
        }

        impl Tr for Donator {
            #[paralegal::marker(source, return)]
            fn source(&self) -> usize { 0 }
            fn target<T>(&self, t: T) {}
        }

        impl Tr for Receiver {
            fn source(&self) -> usize { 0 }
            #[paralegal::marker(target, arguments = [1])]
            fn target<T>(&self, t: T) {}
        }

        fn connect(give: impl Tr, take: impl Tr) {
            take.target(give.source())
        }

        #[paralegal::analyze]
        fn has_connection() {
            connect(Donator, Receiver);
        }

        #[paralegal::analyze]
        fn has_no_connection() {
            connect(Receiver, Donator);
        }
    ))?;

    test.run(|ctx| {
        ctx.controller_contexts().for_each(|ctx| {
            let sources: Box<[_]> = ctx
                .marked_nodes(Identifier::new_intern("source"))
                .filter(|n| n.controller_id() == ctx.id())
                .collect();
            let targets: Box<[_]> = ctx
                .marked_nodes(Identifier::new_intern("target"))
                .filter(|n| n.controller_id() == ctx.id())
                .collect();

            let expect_connect = ctx.current().name.as_str() == "has_connection";

            assert_error!(
                ctx,
                !expect_connect || !sources.is_empty(),
                "Source presence. Expectation: {}",
                expect_connect
            );
            assert_error!(
                ctx,
                !expect_connect || !targets.is_empty(),
                "Target presence. Expectation: {}",
                expect_connect
            );
            assert_error!(
                ctx,
                !expect_connect
                    || ctx
                        .any_flows(&sources, &targets, EdgeSelection::Data)
                        .is_some(),
                "Flow. Expectation: {}",
                expect_connect
            );
            for &src in sources.iter() {
                ctx.node_note(src, format!("This is a source {}", ctx.describe_node(src)));
            }
            for &src in targets.iter() {
                ctx.node_note(src, format!("This is a target {}", ctx.describe_node(src)));
            }
        });
        Ok(())
    })
}
