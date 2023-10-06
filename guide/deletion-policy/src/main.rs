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

    let found = ctx.desc().controllers.iter().any(|(deleter_id, deleter)| {
        let delete_sinks = ctx
            .marked_sinks(deleter.data_sinks(), Marker::new_intern("deletes"))
            .collect::<Vec<_>>();
        user_data_types.iter().all(|&t| {
            let sources = ctx.srcs_with_type(deleter, t).collect::<Vec<_>>();
            ctx.any_flows(*deleter_id, &sources, &delete_sinks)
                .is_some()
        })
    });
    assert_error!(ctx, found, "Could not find a controller deleting all types");
    Ok(())
}
