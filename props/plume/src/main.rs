use anyhow::Result;
use clap::{Parser, ValueEnum};
use std::sync::Arc;

use paralegal_policy::{paralegal_spdg::traverse::EdgeSelection, Context, Diagnostics, Marker};

macro_rules! marker {
    ($id:ident) => {
        Marker::new_intern(stringify!($id))
    };
}

fn check(ctx: Arc<Context>) -> Result<()> {
    let user_data_types = ctx.marked_type(marker!(user_data));

    let found = ctx.all_controllers().find(|(deleter_id, ctrl)| {
        let delete_sinks = ctx
            .all_nodes_for_ctrl(*deleter_id)
            .filter(|n| ctx.has_marker(marker!(to_delete), *n))
            .collect::<Vec<_>>();
        user_data_types.iter().all(|&t| {
            let sources = ctx.srcs_with_type(*deleter_id, t).collect::<Vec<_>>();
            if ctx
                .any_flows(&sources, &delete_sinks, EdgeSelection::Data)
                .is_none()
            {
                let mut note = ctx.struct_note(format!(
                    "The type {} is not being deleted in {}",
                    ctx.desc().type_info[&t].rendering,
                    ctrl.name
                ));
                for src in sources {
                    note.with_node_note(src, "This is a source for that type");
                }
                for snk in &delete_sinks {
                    note.with_node_note(*snk, "This is a potential delete sink");
                }
                note.emit();
                false
            } else {
                true
            }
        })
    });
    if found.is_none() {
        ctx.error("Could not find a function deleting all types");
    }
    if let Some((found, _)) = found {
        println!(
            "Found {} deletes all user data types",
            ctx.desc().controllers[&found].name
        );
        for t in user_data_types {
            println!("Found user data {}", ctx.describe_def(*t));
        }
    }
    Ok(())
}

#[derive(Clone, Copy, ValueEnum, PartialOrd, Ord, PartialEq, Eq)]
#[clap(rename_all = "kebab-case")]
enum PlumeVersion {
    /// Original, Deletes no comments
    V0,
    /// Deleted comments
    V1,
    /// What the policy should be: requires media deletion
    V2,
    /// If the media deletion was fixed
    V3,
}

#[derive(clap::Parser)]
struct Args {
    plume_dir: std::path::PathBuf,
    /// Which plume version to run.
    ///
    /// - `v0` is the original version that deletes no comments
    /// - `v1` deletes the comments
    /// - `v2` includes the requirement to delete media
    /// - `v3` also ensures the media is deleted
    #[clap(long, short = 'p', default_value_t = PlumeVersion::V0, value_enum)]
    plume_version: PlumeVersion,
    /// Additional arguments to pass to cargo, this is intended to be used to
    /// enable the features that toggle the bugs, like `delete-comments`.
    #[clap(last = true)]
    cargo_args: Vec<String>,
}

fn main() -> Result<()> {
    let args = Args::try_parse()?;

    let mut cmd = paralegal_policy::SPDGGenCommand::global();
    cmd.get_command().args([
        "--external-annotations",
        "external-annotations.toml",
        "--abort-after-analysis",
        "--target",
        "plume-models",
        "--",
        "--no-default-features",
        "--features",
        "postgres",
    ]);
    for (version_bound, feature) in [
        (PlumeVersion::V1, "delete-comments"),
        (PlumeVersion::V2, "require-delete-media"),
        (PlumeVersion::V3, "delete-media"),
    ] {
        if args.plume_version >= version_bound {
            cmd.get_command()
                .args(["--features", &format!("plume-models/{feature}")]);
        }
    }
    cmd.get_command().args(args.cargo_args);
    let result = cmd.run(args.plume_dir)?.with_context(check)?;
    println!(
        "Finished {}successfully with {}",
        if result.success { "" } else { "un" },
        result.stats
    );
    if !result.success {
        std::process::exit(1);
    }
    Ok(())
}
