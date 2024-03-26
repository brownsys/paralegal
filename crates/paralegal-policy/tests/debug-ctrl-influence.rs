mod helpers;

use helpers::{Result, Test};
use paralegal_policy::{loc, Diagnostics, Marker};

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
