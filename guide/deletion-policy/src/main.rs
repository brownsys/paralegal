use anyhow::Result;
use paralegal_policy::{assert_error, Context, Marker};
use std::sync::Arc;

fn dummy_policy(ctx: Arc<Context>) -> Result<()> {
    println!("Graph loaded.");
    Ok(())
}

fn main() -> Result<()> {
    let dir = "../file-db-example/";
    let mut cmd = paralegal_policy::SPDGGenCommand::global();
    cmd.get_command().args([
        "--external-annotations",
        "external-annotations.toml",
        "--eager-local-markers",
    ]);
    cmd.run(dir)?.with_context(dummy_policy)?;
    println!("Policy successful");
    Ok(())
}

fn deletion_policy(ctx: Arc<Context>) -> Result<()> {
    let user_data_types = ctx
        .marked_type(Marker::new_intern("user_data"))
        .collect::<Vec<_>>();

    let found = ctx.all_controllers().any(|(deleter_id, _)| {
        let delete_sinks = ctx
            .all_nodes_for_ctrl(&deleter_id)
            .filter(|n| ctx.has_marker(Marker::new_intern("deletes"), n))
            .collect::<Vec<_>>();
        user_data_types.iter().all(|&t| {
            let sources = ctx.srcs_with_type(&deleter_id, t).collect::<Vec<_>>();
            ctx.any_flows(
                &sources.iter().collect::<Vec<_>>(),
                &delete_sinks.iter().collect::<Vec<_>>(),
                paralegal_policy::EdgeType::Data,
            )
            .is_some()
        })
    });
    assert_error!(ctx, found, "Could not find a controller deleting all types");
    Ok(())
}
