use anyhow::Result;
use std::sync::Arc;

use paralegal_policy::{
    paralegal_spdg::{rustc_portable::DefId, Ctrl, DataSink, DataSource, DefKind},
    Context, ControllerId, Marker,
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
    fn controllers<'a>(&'a self) -> Box<dyn Iterator<Item = (ControllerId, &'a Ctrl)> + 'a>;
    fn marked_type<'a>(&'a self, marker: Marker) -> Box<dyn Iterator<Item = DefId> + 'a>;
    fn describe_def(&self, def_id: DefId) -> DisplayDef;
    fn any_flows<'a>(
        &self,
        ctrl_id: ControllerId,
        from: &[&'a DataSource],
        to: &[&'a DataSink],
    ) -> Option<(&'a DataSource, &'a DataSink)>;
}

impl ContextExt for Context {
    fn controllers<'a>(&'a self) -> Box<dyn Iterator<Item = (ControllerId, &'a Ctrl)> + 'a> {
        Box::new(self.desc().controllers.iter().map(|(k, v)| (*k, v))) as Box<_>
    }

    fn marked_type<'a>(&'a self, marker: Marker) -> Box<dyn Iterator<Item = DefId> + 'a> {
        Box::new(
            self.marked(marker)
                .filter(|(did, _)| self.desc().def_info[did].kind == DefKind::Type)
                .map(|(did, refinement)| {
                    assert!(refinement.on_self());
                    *did
                }),
        ) as Box<_>
    }
    fn describe_def(&self, def_id: DefId) -> DisplayDef {
        DisplayDef { ctx: self, def_id }
    }

    fn any_flows<'a>(
        &self,
        ctrl_id: ControllerId,
        from: &[&'a DataSource],
        to: &[&'a DataSink],
    ) -> Option<(&'a DataSource, &'a DataSink)> {
        from.iter().find_map(|&src| {
            to.iter()
                .find_map(|&sink| self.flows_to(ctrl_id, src, sink).then_some((src, sink)))
        })
    }
}

fn check(ctx: Arc<Context>) -> Result<()> {
    let user_data_types = ctx.marked_type(marker!(user_data)).collect::<Vec<_>>();

    let found = ctx
        .controllers()
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
