use std::sync::Arc;

use anyhow::{Ok, Result};
use helpers::Test;
use paralegal_policy::{Context, Diagnostics, EdgeSelection, NodeQueries};
use paralegal_spdg::Identifier;

mod helpers;

const CODE: &str = include_str!("raw-code/contile.rs");

fn policy(ctx: Arc<Context>) -> Result<()> {
    let m_sink = Identifier::new_intern("sink");
    let m_sensitive = Identifier::new_intern("sensitive");
    let m_send = Identifier::new_intern("metrics_server");
    ctx.clone().named_policy(
        Identifier::new_intern("personal tags not in metrics"),
        |ctx| {
            for sink in ctx.nodes_marked_any_way(m_sink) {
                for src in ctx.nodes_marked_any_way(m_sensitive) {
                    let mut intersections = sink
                        .influencers(&ctx, EdgeSelection::Data)
                        .into_iter()
                        .filter(|intersection| {
                            src.flows_to(*intersection, &ctx, EdgeSelection::Data)
                        });
                    if let Some(intersection) = intersections.next() {
                        let mut msg = ctx
                            .struct_node_error(intersection, "This call releases sensitive data");
                        msg.with_node_note(src, "Sensitive data originates here");
                        msg.with_node_note(intersection, "Externalizing value originates here");
                        msg.emit();
                    }
                }
            }
            Ok(())
        },
    )?;
    ctx.named_policy(Identifier::new_intern("personal tags not sent"), |ctx| {
        let personals = ctx.nodes_marked_any_way(m_sensitive).collect::<Box<[_]>>();
        let sends = ctx.nodes_marked_any_way(m_send).collect::<Box<[_]>>();
        if let Some((from, to)) = ctx.any_flows(&personals, &sends, EdgeSelection::Data) {
            ctx.always_happens_before([from], |_| false, |t| t == to)?
                .report(ctx);
            // let mut msg = ctx.struct_node_error(to, "This call externalizes a sensitive value");
            // msg.with_node_note(from, "Sensitive data originates here");
            // msg.emit();
        }
        Ok(())
    })
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

    // test.with_dep([
    //     "actix-web-location@0.7",
    //     "--features",
    //     "actix-web-v4,maxmind,cadence",
    // ]);
    test.run(policy)
}
