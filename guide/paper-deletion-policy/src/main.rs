use anyhow::Result;
use paralegal_policy::{
    assert_error, paralegal_spdg::traverse::EdgeSelection, Context, Marker, NodeExt, Eval, src
};
use std::sync::Arc;

fn dummy_policy(_ctx: Arc<Context>) -> Result<()> {
    println!("Graph loaded.");
    Ok(())
}

fn main() -> Result<()> {
    let dir = "../paper-deletion-example/";
    paralegal_policy::SPDGGenCommand::global()
        .external_annotations("external-annotations.toml")
        .abort_after_analysis()
        .run(dir)?
        .with_context(dummy_policy)?;
    println!("Policy successful");
    Ok(())
}

#[allow(dead_code)]
fn paper_deletion_policy(ctx: Arc<Context>) -> Result<()> {
    let my_policy_result = Eval::any(ctx.all_controllers().collect(), |(deleter_id, _ignored)| {
        Eval::all(
            ctx.marked_type(Marker::new_intern("user_data"))
                .iter()
                .collect(),
            |&t| {
                Eval::any(ctx.srcs_with_type(deleter_id, t).collect(), |src| {
                    Eval::any(
                        ctx.all_nodes_for_ctrl(deleter_id)
                            .filter(|n| ctx.has_marker(Marker::new_intern("make_delete_query"), *n))
                            .collect::<Vec<_>>(),
                        |sink| Eval::and(
                            src!(ctx.flows_to(src, sink, EdgeSelection::Data)),
                            Eval::any(
                                ctx.all_nodes_for_ctrl(deleter_id)
                                    .filter(|n| ctx.has_marker(Marker::new_intern("executes"), *n))
                                    .collect::<Vec<_>>(),
                                |exec| {
                                    src!(ctx.flows_to(sink, exec, EdgeSelection::Data))
                                })
                        )
                    )
                })
            },
        )
    });
    my_policy_result.emit("", true);
    Ok(())
}