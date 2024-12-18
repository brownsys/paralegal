use anyhow::Result;
use paralegal_policy::{
    assert_error, paralegal_spdg::traverse::EdgeSelection, Marker, NodeExt, RootContext,
};
use std::sync::Arc;

fn dummy_policy(_ctx: Arc<RootContext>) -> Result<()> {
    println!("Graph loaded.");
    Ok(())
}

fn main() -> Result<()> {
    let dir = "../file-db-example/";
    paralegal_policy::SPDGGenCommand::global()
        .external_annotations("external-annotations.toml")
        .run(dir)?
        .with_context(dummy_policy)?;
    println!("Policy successful");
    Ok(())
}

#[allow(dead_code)]
fn deletion_policy(ctx: Arc<RootContext>) -> Result<()> {
    let user_data_types = ctx.marked_type(Marker::new_intern("user_data"));

    let found = ctx.all_controllers().any(|(deleter_id, _ignored)| {
        let delete_sinks = ctx
            .all_nodes_for_ctrl(deleter_id)
            .filter(|n| n.has_marker(&ctx, Marker::new_intern("deletes")))
            .collect::<Vec<_>>();
        user_data_types.iter().all(|&t| {
            let sources = ctx.srcs_with_type(deleter_id, t).collect::<Vec<_>>();
            ctx.any_flows(&sources, &delete_sinks, EdgeSelection::Data)
                .is_some()
        })
    });
    assert_error!(ctx, found, "Could not find a controller deleting all types");
    Ok(())
}
