#![feature(rustc_private)]

use std::sync::Arc;

use anyhow::{Ok, Result};
use helpers::Test;
use paralegal_policy::{Context, Diagnostics, EdgeSelection, NodeExt, RootContext};
use paralegal_spdg::Identifier;

mod helpers;

const CODE: &str = include_str!("raw-code/contile.rs");

fn policy(ctx: Arc<RootContext>) -> Result<()> {
    let m_sink = Identifier::new_intern("sink");
    let m_sensitive = Identifier::new_intern("sensitive");
    let m_send = Identifier::new_intern("metrics_server");
    let mut failures = 0;
    ctx.clone().named_policy(
        Identifier::new_intern("personal tags not sent to adm"),
        |ctx| {
            for sink in ctx.nodes_marked_any_way(m_sink) {
                for src in ctx.nodes_marked_any_way(m_sensitive) {
                    if let Some(path) = src.shortest_path(sink, &ctx, EdgeSelection::Data) {
                        let mut msg =
                            ctx.struct_node_error(sink, "this call sends personal data to the adm");
                        msg.with_node_help(src, "personal data originates here");
                        for n in path.iter() {
                            msg.with_node_note(
                                *n,
                                format!("Passes through this {}", n.info(&ctx).description),
                            );
                        }
                        msg.emit();
                        failures += 1;
                    }
                }
            }

            Ok(())
        },
    )?;
    ctx.named_policy(
        Identifier::new_intern("personal tags not sent to metrics"),
        |ctx| {
            let personals = ctx.nodes_marked_any_way(m_sensitive).collect::<Box<[_]>>();
            let sends = ctx.nodes_marked_any_way(m_send).collect::<Box<[_]>>();
            for personal in personals.iter() {
                for send in sends.iter() {
                    if let Some(path) = personal.shortest_path(*send, &ctx, EdgeSelection::Data) {
                        let mut msg = ctx.struct_node_error(
                            *send,
                            "this call sends personal data to the metrics server",
                        );
                        msg.with_node_note(*personal, "personal data originates here");
                        for p in path.iter() {
                            msg.with_node_note(
                                *p,
                                format!("Passes through this {}", p.info(&ctx).description),
                            );
                        }
                        msg.emit();
                        failures += 1;
                    }
                }
            }
            Ok(())
        },
    )?;
    println!("Found {failures} violations");
    Ok(())
}

#[ignore = "WIP"]
#[test]
fn overtaint() -> Result<()> {
    let mut test = Test::new(CODE)?;
    // test.with_dep(["chrono@0.4"]);
    test.with_dep(["reqwest@0.11", "--features", "json"]);
    test.with_dep([
        "actix-web@4",
        "--no-default-features",
        "--features",
        "macros",
    ]);
    test.with_dep(["cadence@0.29"]);
    test.with_dep(["tokio@1", "--features", "macros,sync"]);

    // test.with_dep([
    //     "actix-web-location@0.7",
    //     "--features",
    //     "actix-web-v4,maxmind,cadence",
    // ]);
    test.with_dep(["serde@1", "--features", "derive"]);
    test.with_external_annotations(
        "
[[\"cadence::builder::MetricBuilder::send\"]]
marker = \"metrics_server\"
on_argument = [0]

[[\"cadence::builder::MetricBuilder::try_send\"]]
marker = \"metrics_server\"
on_argument = [0]
    ",
    );
    test.run(policy)
}
