mod helpers;

use helpers::{Result, Test};
use paralegal_policy::{
    algo::ahb, loc, paralegal_spdg, Context, Diagnostics, Marker, NodeExt, NodeQueries,
};
use paralegal_spdg::traverse::EdgeSelection;
macro_rules! marker {
    ($id:ident) => {
        Marker::new_intern(stringify!($id))
    };
}

#[test]
fn email_send_overtaint() -> Result<()> {
    let mut test = Test::new(stringify!(
        struct ApiKey {
            user: String,
        }

        #[paralegal::marker(safe_source)]
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

        #[paralegal::marker(sensitive)]
        struct Data {
            answers: Vec<(String, String)>,
        }

        #[paralegal::marker(safe_source_with_bless, return)]
        fn get_staff(config: &Config) -> Vec<String> {
            unimplemented!()
        }

        #[paralegal::marker(safe_source, return)]
        fn get_admins(config: &Config) -> Vec<String> {
            unimplemented!()
        }

        #[paralegal::analyze]
        #[paralegal::marker(bless_safe_source, arguments = [2])]
        fn main(apikey: ApiKey, config: &Config, num: u8, bg: Backend, data: &Data) {
            let mut recipients: Vec<String> = vec![];
            let recipients = if num < 90 {
                get_staff(config)
            } else {
                get_admins(config)
            };
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
            .unwrap()
        }

        #[paralegal::marker{ sink, arguments = [3, 4] }]
        #[paralegal::marker{ scopes, arguments = [2] }]
        fn my_send(
            log: Logger,
            sender: String,
            recipients: Vec<String>,
            subject: String,
            text: String,
        ) -> Result<(), String> {
            Ok(())
        }
    ))?;
    test.context_config().always_happens_before_tracing = ahb::TraceLevel::Full;

    test.run(|cx| {
        for c_id in cx.desc().controllers.keys() {
            // All srcs that have no influencers
            let roots = cx.roots(*c_id, EdgeSelection::Data).collect::<Vec<_>>();

            let safe_scopes = cx
                // All nodes marked "safe"
                .all_nodes_for_ctrl(*c_id)
                .filter(|n| n.has_marker(&cx, marker!(safe_source)))
                // And all nodes marked "safe_with_bless"
                .chain(cx.all_nodes_for_ctrl(*c_id).filter(|node| {
                    node.has_marker(&cx, marker!(safe_source_with_bless))
                        && node
                            // That are influenced by a node marked "bless"
                            .influencers(&cx, EdgeSelection::Both)
                            .into_iter()
                            .any(|b| b.has_marker(&cx, marker!(bless_safe_source)))
                }))
                .collect::<Vec<_>>();
            let sinks = cx
                .all_nodes_for_ctrl(*c_id)
                .filter(|n| n.has_marker(&cx, marker!(sink)))
                .collect::<Vec<_>>();
            let mut sensitives = cx
                .all_nodes_for_ctrl(*c_id)
                .filter(|node| node.has_marker(&cx, marker!(sensitive)));

            let some_failure = sensitives.any(|sens| {
                sinks.iter().any(|sink| {
                    // sensitive flows to store implies
                    if !sens.flows_to(*sink, &cx, EdgeSelection::Data) {
                        return false;
                    }

                    let call_sites = sink.consuming_call_sites(&cx).collect::<Box<[_]>>();
                    let [cs] = call_sites.as_ref() else {
                        cx.node_error(
                            *sink,
                            format!(
                                "Unexpected number of call sites {} for this node",
                                call_sites.len()
                            ),
                        );
                        return false;
                    };
                    let sink_callsite = cx.inputs_of(*cs);

                    println!("{cs}");

                    // scopes for the store
                    let store_scopes = cx
                        .influencers(&sink_callsite, EdgeSelection::Data)
                        .filter(|n| n.has_marker(&cx, marker!(scopes)))
                        .collect::<Vec<_>>();
                    if store_scopes.is_empty() {
                        cx.node_error(*sink, loc!("Did not find any scopes for this sink"));
                    }

                    // all flows are safe before scope
                    let safe_before_scope = cx
                        .always_happens_before(
                            roots.iter().cloned(),
                            |n| safe_scopes.contains(&n),
                            |n| store_scopes.contains(&n),
                        )
                        .unwrap();

                    safe_before_scope.report(cx.clone());

                    !safe_before_scope.holds()
                })
            });

            if some_failure {
                let mut nodes = cx.marked_nodes(marker!(scopes)).peekable();
                if nodes.peek().is_none() {
                    let mut err = cx.struct_help(loc!("No suitable scopes were found"));

                    for scope in nodes {
                        err.with_node_note(scope, "This location would have been a suitable scope");
                    }

                    err.emit();
                }
            }
        }
        Ok(())
    })
}
