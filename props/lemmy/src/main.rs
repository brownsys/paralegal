extern crate anyhow;

use anyhow::Result;
use clap::{Parser, ValueEnum};
use std::io::stdout;
use std::iter::Filter;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, Instant};

use paralegal_policy::{
    assert_error, loc,
    paralegal_spdg::{traverse::EdgeSelection, GlobalNode, Identifier},
    Context, Diagnostics, Marker, PolicyContext,
};

macro_rules! marker {
    ($id:ident) => {
        Marker::new_intern(stringify!($id))
    };
}

pub struct CommunityProp {
    cx: Arc<PolicyContext>,
    args: &'static Arguments,
}

pub struct InstanceProp {
    cx: Arc<PolicyContext>,
    args: &'static Arguments,
}

impl CommunityProp {
    fn new(cx: Arc<PolicyContext>, args: &'static Arguments) -> Self {
        CommunityProp { cx, args }
    }

    fn check(&mut self) -> Result<()> {
        let ctx = &self.cx;
        let mut community_writes = self.cx.marked_nodes(marker!(db_community_write));
        let mut delete_check = marker!(community_delete_check);
        let mut ban_check = marker!(community_ban_check);

        for write in community_writes {
            if !ctx
                .influencers(write, EdgeSelection::Both)
                .any(|i| ctx.has_marker(ban_check, i))
            {
                ctx.node_error(write, "This write has no ban check")
            }
            if !ctx
                .influencers(write, EdgeSelection::Both)
                .any(|i| ctx.has_marker(delete_check, i))
            {
                ctx.node_error(write, "This write has no delete check")
            }
        }

        Ok(())
    }
}

impl InstanceProp {
    fn new(cx: Arc<PolicyContext>, args: &'static Arguments) -> Self {
        InstanceProp { cx, args }
    }

    fn check(&mut self) -> Result<()> {
        let ctx = &self.cx;
        let instance_delete = Identifier::new_intern("instance_delete_check");
        let instance_ban = Identifier::new_intern("instance_ban_check");
        let accesses = ctx
            .marked_nodes(Identifier::new_intern("db_access"))
            .filter(|n| !ctx.has_marker(Identifier::new_intern("db_user_read"), *n))
            .collect::<Vec<_>>();

        for access in accesses {
            if !ctx
                .influencers(access, EdgeSelection::Both)
                .any(|n| ctx.has_marker(instance_delete, n))
            {
                ctx.node_error(access, "No delete check found for this access");
            }
            if !ctx
                .influencers(access, EdgeSelection::Both)
                .any(|n| ctx.has_marker(instance_ban, n))
            {
                ctx.node_error(access, "No ban check found for this access");
            }
        }

        Ok(())
    }
}

#[derive(ValueEnum, Copy, Clone, Debug)]
enum Prop {
    Community,
    Instance,
}

impl Prop {
    fn run(self, cx: Arc<Context>, args: &'static Arguments) -> anyhow::Result<()> {
        match self {
            Self::Community => cx.named_policy(Identifier::new_intern("Community Policy"), |cx| {
                CommunityProp::new(cx.clone(), args).check()
            }),
            Self::Instance => cx.named_policy(Identifier::new_intern("Instance Policy"), |cx| {
                InstanceProp::new(cx.clone(), args).check()
            }),
        }
    }
}

#[derive(Parser)]
struct Arguments {
    path: PathBuf,
    #[clap(long)]
    skip_compile: bool,
    /// Property selection. If none are selected all are run
    #[clap(long)]
    prop: Vec<Prop>,
    #[clap(long, short)]
    quiet: bool,
    #[clap(last = true)]
    extra_args: Vec<String>,
}

fn main() -> anyhow::Result<()> {
    let args: &'static Arguments = Box::leak(Box::new(Arguments::parse()));

    let graph_file = if args.skip_compile {
        paralegal_policy::GraphLocation::std(&args.path)
    } else {
        let mut cmd = paralegal_policy::SPDGGenCommand::global();
        cmd.external_annotations("external-annotations.toml");
        cmd.abort_after_analysis();
        cmd.get_command().arg("--target").arg("lemmy_api");
        cmd.get_command().args(&args.extra_args);
        cmd.run(&args.path)?
    };

    let res = graph_file.with_context(|cx| {
        let num_controllers = cx.desc().controllers.len();
        let sum_nodes = cx
            .desc()
            .controllers
            .values()
            .map(|spdg| spdg.graph.node_count())
            .sum::<usize>();
        println!(
            "Analyzing over {num_controllers} controllers with avg {} nodes per graph",
            sum_nodes / num_controllers
        );
        for ctrl in cx.desc().controllers.values() {
            let num_nodes = ctrl.graph.node_count();
            if num_nodes < 1000 {
                println!(
                    "{} has only {num_nodes} nodes",
                    paralegal_policy::paralegal_spdg::DisplayPath::from(&ctrl.path)
                );
            }
        }
        for p in if args.prop.is_empty() {
            Prop::value_variants()
        } else {
            args.prop.as_slice()
        } {
            p.run(cx.clone(), args)?;
        }

        anyhow::Ok(())
    })?;

    println!("Policy finished. Stats {}", res.stats);
    if !res.success {
        std::process::exit(1);
    }
    anyhow::Ok(())
}
