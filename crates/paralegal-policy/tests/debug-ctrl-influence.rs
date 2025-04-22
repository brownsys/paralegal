mod helpers;

use helpers::{Result, Test};
use paralegal_policy::{assert_error, loc, Context, Diagnostics, Marker, NodeQueries};
use paralegal_spdg::{Identifier, IntoIterGlobalNodes, NodeCluster};

macro_rules! marker {
    ($id:ident) => {
        Marker::new_intern(stringify!($id))
    };
}

#[test]
fn has_ctrl_flow_influence() -> Result<()> {
    let test = Test::new(stringify!(
        struct ApiKey {
            user: String,
        }

        struct Config {
            a: usize,
            b: usize,
            class: u32,
        }

        #[derive(Clone)]
        struct Logger(std::path::PathBuf);

        struct Backend {
            log: Logger,
        }

        struct Data {
            answers: Vec<(String, String)>,
        }

        #[paralegal::marker(auth_check, return)]
        async fn get_admins(config: &Config) -> Result<Vec<String>, String> {
            unimplemented!()
        }

        #[paralegal::analyze]
        async fn main(
            apikey: ApiKey,
            config: &Config,
            num: u8,
            bg: Backend,
            data: &Data,
        ) -> Result<Vec<String>, String> {
            let mut recipients: Vec<String> = vec![];
            // NOTE: this line causes a "too many candidates for the return" warning
            // but the policy does pass/fail with/without this line, as expected
            get_admins(config).await?;
            let answer_log = format!(
                "{}",
                data.answers
                    .iter()
                    .map(|(i, t)| format!("Question {}:\n{}", i, t))
                    .collect::<Vec<_>>()
                    .join("\n-----\n")
            );
            my_send(
                bg.log.clone(),
                apikey.user.clone(),
                recipients,
                format!("{} meeting {} questions", config.class, num),
                answer_log,
            )
            .await
            .unwrap();

            Ok(vec![])
        }

        #[paralegal::marker(sink, return)]
        async fn my_send(
            log: Logger,
            sender: String,
            recipients: Vec<String>,
            subject: String,
            text: String,
        ) -> Result<(), String> {
            Ok(())
        }
    ))?;
    test.run(|cx| {
        for _c_id in cx.desc().controllers.keys() {
            let mut auth_checks = cx.marked_nodes(marker!(auth_check));
            let mut sinks = cx.marked_nodes(marker!(sink));

            let ok = sinks.all(|sink| auth_checks.any(|check| cx.has_ctrl_influence(check, sink)));

            if !ok {
                let mut err = cx.struct_help(loc!("No auth check authorizing sink"));

                let sinks = cx.marked_nodes(marker!(sink));
                let auth_checks = cx.marked_nodes(marker!(auth_check));

                for sink in sinks {
                    err.with_node_note(sink, "This is a sink");
                }

                for check in auth_checks {
                    err.with_node_note(check, "This is an auth check");
                }

                err.emit();
            }
        }
        Ok(())
    })
}

#[test]
fn lemmy_ctrl_influence() -> Result<()> {
    Test::new(stringify!(
        #[paralegal::marker(check, return)]
        async fn check_safe(data: usize) -> Result<(), ()> {
            Ok(())
        }

        #[paralegal::marker(sensitive, return)]
        async fn sensitive_action(data: usize) {}

        #[paralegal::analyze]
        async fn main(data: usize) -> Result<(), ()> {
            check_safe(data).await?;

            sensitive_action(data).await;
            Ok(())
        }
    ))?
    .run(|ctx| {
        let mut sensitive = ctx
            .marked_nodes(Identifier::new_intern("sensitive"))
            .peekable();
        let checks = ctx
            .marked_nodes(Identifier::new_intern("check"))
            .collect::<Box<_>>();

        assert!(sensitive.peek().is_some());
        assert!(!checks.is_empty());

        assert_error!(
            ctx,
            sensitive.all(|sens| { checks.iter().any(|c| c.has_ctrl_influence(sens, &ctx)) })
        );
        Ok(())
    })
}

#[test]
fn lemmy_blocking_ctrl_influence() -> Result<()> {
    Test::new(stringify!(
        #[paralegal::marker(check, return)]
        async fn check_safe(data: usize) -> Result<(), ()> {
            Ok(())
        }

        #[paralegal::marker(sensitive, return)]
        fn sensitive_action(data: usize) {}

        async fn blocking(f: impl FnOnce() -> ()) {
            f()
        }

        #[paralegal::analyze]
        async fn main(data: usize) -> Result<(), ()> {
            check_safe(data).await?;

            blocking(|| {
                sensitive_action(data);
            })
            .await;
            Ok(())
        }
    ))?
    .run(|ctx| {
        let mut sensitive = ctx
            .marked_nodes(Identifier::new_intern("sensitive"))
            .peekable();
        let checks = ctx
            .marked_nodes(Identifier::new_intern("check"))
            .collect::<Box<_>>();

        assert!(sensitive.peek().is_some());
        assert!(!checks.is_empty());

        assert_error!(
            ctx,
            sensitive.all(|sens| { checks.iter().any(|c| c.has_ctrl_influence(sens, &ctx)) })
        );
        Ok(())
    })
}

#[test]
fn nested_ctrl_influence() -> Result<()> {
    Test::new(stringify!(
        #[paralegal::marker(check, return)]
        async fn check_safe(data: usize) -> Result<(), ()> {
            Ok(())
        }

        #[paralegal::marker(sensitive, return)]
        fn sensitive_action(data: usize) {}

        async fn blocking(data: usize) {
            sensitive_action(data)
        }

        #[paralegal::analyze]
        async fn main(data: usize) -> Result<(), ()> {
            check_safe(data).await?;

            blocking(data).await;
            Ok(())
        }
    ))?
    .run(|ctx| {
        let mut sensitive = ctx
            .marked_nodes(Identifier::new_intern("sensitive"))
            .peekable();
        let checks = ctx
            .marked_nodes(Identifier::new_intern("check"))
            .collect::<Box<_>>();

        assert!(sensitive.peek().is_some());
        assert!(!checks.is_empty());

        assert_error!(
            ctx,
            sensitive.all(|sens| { checks.iter().any(|c| c.has_ctrl_influence(sens, &ctx)) })
        );
        Ok(())
    })
}

#[test]
fn nested_ctrl_influence_2() -> Result<()> {
    Test::new(stringify!(
        #[paralegal::marker(check, return)]
        async fn check_safe(data: usize) -> Result<(), ()> {
            Ok(())
        }

        #[paralegal::marker(sensitive, return)]
        fn sensitive_action(data: usize) {}

        async fn blocking(data: usize) {
            sensitive_action(data)
        }

        #[paralegal::analyze]
        async fn main(data: usize) -> Result<(), ()> {
            check_safe(data).await?;

            blocking(data).await;
            Ok(())
        }
    ))?
    .run(|ctx| {
        let sensitive =
            NodeCluster::try_from_iter(ctx.marked_nodes(Identifier::new_intern("sensitive")))
                .unwrap();
        let checks =
            NodeCluster::try_from_iter(ctx.marked_nodes(Identifier::new_intern("check"))).unwrap();

        if let Some(unreached) = checks.has_ctrl_influence_all(&sensitive, &ctx) {
            let mut msg = ctx.struct_error("Some nodes were not protected");
            for node in unreached.iter_global_nodes() {
                msg.with_node_note(node, "This node was not protected");
            }
            msg.emit();
        }
        Ok(())
    })
}

#[test]
fn double_nested_ctrl_influence() -> Result<()> {
    Test::new(stringify!(
        #[paralegal::marker(check, return)]
        fn check_safe(data: usize) -> Result<(), ()> {
            Ok(())
        }

        #[paralegal::marker(sensitive, return)]
        fn sensitive_action(data: usize) {}

        fn blocking(data: usize) {
            wrap(data)
        }

        fn wrap(data: usize) {
            sensitive_action(data)
        }

        #[paralegal::analyze]
        fn main(data: usize) -> Result<(), ()> {
            check_safe(data)?;

            blocking(data);
            Ok(())
        }
    ))?
    .run(|ctx| {
        let mut sensitive = ctx
            .marked_nodes(Identifier::new_intern("sensitive"))
            .peekable();
        let checks = ctx
            .marked_nodes(Identifier::new_intern("check"))
            .collect::<Box<_>>();

        assert!(sensitive.peek().is_some());
        assert!(!checks.is_empty());

        assert_error!(
            ctx,
            sensitive.all(|sens| { checks.iter().any(|c| c.has_ctrl_influence(sens, &ctx)) })
        );
        Ok(())
    })
}
