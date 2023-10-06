use anyhow::Result;
use std::sync::Arc;

use paralegal_policy::{
    paralegal_spdg::{rustc_portable::DefId, Ctrl, DataSink, DataSource, DefKind},
    Context, ControllerId, Diagnostics, Marker,
};

macro_rules! marker {
    ($id:ident) => {
        Marker::new_intern(stringify!($id))
    };
}

struct DisplayDef<'a> {
    def_id: DefId,
    ctx: &'a Context,
}

impl<'a> std::fmt::Display for DisplayDef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Write;
        let info = &self.ctx.desc().def_info[&self.def_id];
        f.write_str(match info.kind {
            DefKind::Type => "type",
            DefKind::Function => "function",
        })?;
        f.write_str(" `")?;
        for segment in &info.path {
            f.write_str(segment.as_str())?;
            f.write_str("::")?;
        }
        f.write_str(info.name.as_str())?;
        f.write_char('`')
    }
}

trait ContextExt {
    fn describe_def(&self, def_id: DefId) -> DisplayDef;
}

impl ContextExt for Context {
    fn describe_def(&self, def_id: DefId) -> DisplayDef {
        DisplayDef { ctx: self, def_id }
    }
}

fn check(ctx: Arc<Context>) -> Result<()> {
    let user_data_types = ctx.marked_type(marker!(user_data)).collect::<Vec<_>>();

    let found = ctx
        .all_controllers()
        .collect::<Vec<_>>()
        .into_iter()
        .find(|(deleter_id, deleter)| {
            let delete_sinks = ctx
                .marked_sinks(deleter.data_sinks(), marker!(to_delete))
                .collect::<Vec<_>>();
            user_data_types.iter().all(|&t| {
                let sources = ctx.srcs_with_type(deleter, t).collect::<Vec<_>>();
                ctx.any_flows(*deleter_id, &sources, &delete_sinks)
                    .is_some()
            })
        });
    if found.is_none() {
        ctx.error("Could not find a function deleting all types");
    }
    if let Some((found, _)) = found {
        println!(
            "Found {} deletes all user data types",
            ctx.describe_def(found)
        );
        for t in user_data_types {
            println!("Found user data {}", ctx.describe_def(t));
        }
    }
    Ok(())
}

#[derive(clap::Parser)]
struct Args {
    plume_dir: std::path::PathBuf,
    /// Additional arguments to pass to cargo, this is intended to be used to
    /// enable the features that toggle the bugs, like `delete-comments`.
    #[clap(last = true)]
    cargo_args: Vec<String>,
}

fn main() -> Result<()> {
    use clap::Parser;
    let args = Args::try_parse()?;

    let mut cmd = paralegal_policy::SPDGGenCommand::global();
    cmd.get_command().args([
        "--external-annotations",
        "external-annotations.toml",
        "--abort-after-analysis",
        "--inline-elision",
        "--target",
        "plume_models",
        "--eager-local-markers",
        "--",
        "--no-default-features",
        "--features",
        "postgres",
        "-p",
        "plume-models",
    ]);
    cmd.get_command().args(args.cargo_args);
    cmd.run(args.plume_dir)?.with_context(check)?;
    println!("Successfully finished");
    Ok(())
}
