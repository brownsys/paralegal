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
}

pub struct InstanceProp {
    cx: Arc<PolicyContext>,
}

impl CommunityProp {
    pub fn new(cx: Arc<PolicyContext>) -> Self {
        CommunityProp { cx }
    }

    pub fn check(&mut self) -> Result<()> {
        let mut community_writes = self.cx.marked_nodes(marker!(db_community_write));
        let mut delete_checks = self.cx.marked_nodes(marker!(community_delete_check));
        let mut ban_checks = self.cx.marked_nodes(marker!(community_ban_check));

        let ok = community_writes.all(|write|
            delete_checks.any(|dc| self.cx.flows_to(dc, write, EdgeSelection::Both))
            &&
            ban_checks.any(|bc| self.cx.flows_to(bc, write, EdgeSelection::Both))
        );
            
        assert_error!(
            self.cx,
            ok,
            "Unauthorized community write"
        );

        Ok(())
    }
}

impl InstanceProp {
    pub fn new(cx: Arc<PolicyContext>) -> Self {
        InstanceProp { cx }
    }

    pub fn check(&mut self) -> Result<()> {
        let mut accesses = self.cx.marked_nodes(marker!(db_access)).filter(|n| !self.cx.has_marker(marker!(db_user_read), *n));
        let mut delete_checks = self.cx.marked_nodes(marker!(instance_delete_check));
        let mut ban_checks = self.cx.marked_nodes(marker!(instance_ban_check));

        let ok = accesses.all(|access| {
            delete_checks.any(|dc| self.cx.flows_to(dc, access, EdgeSelection::Both))
            && 
            ban_checks.any(|bc| self.cx.flows_to(bc, access, EdgeSelection::Both))
        });

        if !ok {
            let mut err = self.cx.struct_help(loc!("No auth check authorizing sink"));

            let accesses = self.cx.marked_nodes(marker!(db_access)).filter(|n| !self.cx.has_marker(marker!(db_user_read), *n));
            let delete_checks = self.cx.marked_nodes(marker!(instance_delete_check));
            let ban_checks = self.cx.marked_nodes(marker!(instance_ban_check));

            for access in accesses {
                err.with_node_note(access, "This is a sink");
            }

            for check in delete_checks {
                err.with_node_note(check, "This is a delete check");

                let influencees : Vec<GlobalNode> = self.cx.influencees(check, EdgeSelection::Both).collect();
                dbg!("There are {} influencees\n", influencees.len());
                for influencee in influencees {
                    // NOTE: problem is that every influencee of check_user_valid is just itself
                    // so it doesn't influence the database access
                    if influencee.controller_id() == check.controller_id() { continue };
                    err.with_node_note(check, "This is an influencee of the delete check");
                }
            }

            for check in ban_checks {
                err.with_node_note(check, "This is a ban check");

                let influencees : Vec<GlobalNode> = self.cx.influencees(check, EdgeSelection::Both).collect();
                dbg!("There are {} influencees\n", influencees.len());
                for influencee in influencees {
                    if influencee.controller_id() == check.controller_id() { continue };
                    err.with_node_note(check, "This is an influencee of the ban check");
                }
            }

            err.emit();
        }

        assert_error!(
            self.cx,
            ok,
            "Unauthorized instance db access"
        );

        Ok(())
    }
}

#[derive(ValueEnum, Copy, Clone, Debug)]
enum Prop {
    Community,
    Instance,
}

impl Prop {
    fn run(self, cx: Arc<Context>) -> anyhow::Result<()> {
        match self {
            Self::Community => cx.named_policy(Identifier::new_intern("Community Policy"), |cx| {
                CommunityProp::new(cx.clone()).check()
            }),
            Self::Instance => cx.named_policy(Identifier::new_intern("Instance Policy"), |cx| {
                InstanceProp::new(cx.clone()).check()
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
            p.run(cx.clone())?;
        }

        anyhow::Ok(())
    })?;

    println!("Policy finished. Stats {}", res.stats);
    if !res.success {
        std::process::exit(1);
    }
    anyhow::Ok(())
}
