#![feature(rustc_private)]

mod helpers;

use anyhow::Result;
use helpers::Test;
use paralegal_policy::{assert_error, Context, Diagnostics, EdgeSelection, NodeExt};
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
            Donator.target(Receiver.source())
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

            let expect_connect = ctx.current().name.as_str() == "connected";

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
                ctx.node_note(src, format!("This is a source {}", src.describe(&ctx)));
            }
            for &src in targets.iter() {
                ctx.node_note(src, format!("This is a target {}", src.describe(&ctx)));
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
                ctx.node_note(src, format!("This is a source {}", src.describe(&ctx)));
            }
            for &src in targets.iter() {
                ctx.node_note(src, format!("This is a target {}", src.describe(&ctx)));
            }
        });
        Ok(())
    })
}

#[test]
fn finding_utc_now() -> Result<()> {
    let mut test = Test::new(stringify!(
        use sled::Db;
        use chrono::Utc;
        use thiserror::Error;

        #[derive(Error, Debug)]
        pub enum AppError {
            #[error("Sled db error: {}", .0)]
            SledError(#[from] sled::Error),
            #[error(transparent)]
            Utf8Error(#[from] std::str::Utf8Error),
        }

        pub async fn clear_invalid(db: &Db, tree_name: &str) -> Result<(), AppError> {
            // let tree = db.open_tree(tree_name)?;
            // for i in tree.iter() {
            //     let (k, _) = i?;
            //     let k_str = std::str::from_utf8(&k)?;
            // let time_stamp = k_str
            //     .split_once('_')
            //     .and_then(|s| i64::from_str_radix(s.0, 16).ok());
            let time_stamp = Some(0_i64);
            if let Some(time_stamp) = time_stamp {
                if time_stamp < Utc::now().timestamp() {
                    panic!()
                    //tree.remove(k)?;
                }
            }
            //}
            Ok(())
        }

        #[paralegal::analyze]
        pub async fn user_chron_job() -> ! {
            let db = sled::Config::default().open().unwrap();
            loop {
                //sleep_seconds(600).await;
                clear_invalid(&db, "dummy").await.unwrap()
                //sleep_seconds(3600 * 4).await;
            }
        }
    ))?;
    test.with_external_annotations(
        "
        [[\"chrono::Utc::now\"]]
        marker = \"time\"
        on_return = true
        ",
    )
    .with_dep([
        "chrono@0.4.38",
        "--no-default-features",
        "--features",
        "clock",
    ])
    .with_dep(["sled@0.34.7"])
    .with_dep(["thiserror@1"]);
    test.run(|ctx| {
        assert_error!(
            ctx,
            ctx.marked_nodes(Identifier::new_intern("time"))
                .next()
                .is_some(),
            "No time found"
        );
        Ok(())
    })
}
