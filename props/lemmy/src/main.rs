extern crate anyhow;

use anyhow::Result;
use clap::Parser;
use std::io::stdout;
use std::iter::Filter;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, Instant};

use paralegal_policy::{
    assert_error,
    paralegal_spdg::{traverse::EdgeSelection, GlobalNode, Identifier},
    Context, Marker, PolicyContext,
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
        let mut community_struct_nodes = self.cx.marked_nodes(marker!(community));
        let mut delete_check_nodes = self.cx.marked_nodes(marker!(community_delete_check));
        let mut ban_check_nodes = self.cx.marked_nodes(marker!(community_ban_check));

        // if some community_struct
        community_struct_nodes.all(|community_struct| {
            // flows to some write
            let community_writes: Vec<GlobalNode> = self
                .cx
                .influencees(community_struct, EdgeSelection::Data)
                .filter(|n| self.cx.has_marker(marker!(db_write), *n))
                .collect();
            // then
            for write in community_writes {
                let has_delete_check = delete_check_nodes.any(|delete_check| {
                    // community struct flows to delete check and
                    self.cx.flows_to(community_struct, delete_check, EdgeSelection::Data) &&
                    // delete check has ctrl flow influence on the write
                    self.cx.has_ctrl_influence(delete_check, write)
                });

                assert_error!(
                    self.cx,
                    has_delete_check,
                    "Unauthorized community write: no delete check"
                );

                let has_ban_check = ban_check_nodes.any(|ban_check| {
                    // community struct flows to ban check and
                    self.cx.flows_to(community_struct, ban_check, EdgeSelection::Data) &&
                    // ban check has ctrl flow influence on the write
                    self.cx.has_ctrl_influence(ban_check, write)
                });

                assert_error!(
                    self.cx,
                    has_ban_check,
                    "Unauthorized community write: no ban check"
                );
            }
            true
        });

        Ok(())
    }
}

impl InstanceProp {
    pub fn new(cx: Arc<PolicyContext>) -> Self {
        InstanceProp { cx }
    }

    pub fn check(&mut self) -> Result<()> {
        let mut writes = self.cx.marked_nodes(marker!(db_write));
        let mut reads = self.cx.marked_nodes(marker!(db_read));
        let mut delete_checks = self.cx.marked_nodes(marker!(instance_delete_check));
        let mut ban_checks = self.cx.marked_nodes(marker!(instance_ban_check));

        // all db writes must be authorized by a ban & delete check
        let has_delete_check = writes.all(|write| {
            delete_checks.any(|dc| self.cx.has_ctrl_influence(dc, write))
                && ban_checks.any(|bc| self.cx.has_ctrl_influence(bc, write))
        });

        assert_error!(
            self.cx,
            has_delete_check,
            "Missing delete check for instance authorization"
        );

        // all db reads (that are not reading the active user) must be authorized by a ban & delete check
        let has_ban_check = reads.all(|read| {
            // you could also implement this by adding .filter(|n| !self.cx.has_marker(marker!(db_user_read), *n)).collect()
            // to line 80 and iterating over those nodes
            if !self.cx.has_marker(marker!(db_user_read), read) {
                delete_checks.any(|dc| self.cx.has_ctrl_influence(dc, read))
                    && ban_checks.any(|bc| self.cx.has_ctrl_influence(bc, read))
            } else {
                true
            }
        });

        assert_error!(
            self.cx,
            has_ban_check,
            "Missing ban check for instance authorization"
        );

        Ok(())
    }
}

#[derive(Parser)]
struct Arguments {
    path: PathBuf,
    #[clap(long)]
    skip_compile: bool,
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
        cx.clone()
            .named_policy(Identifier::new_intern("Community Policy"), |cx| {
                CommunityProp::new(cx.clone()).check()
            })?;
        cx.clone()
            .named_policy(Identifier::new_intern("Instance Policy"), |cx| {
                InstanceProp::new(cx.clone()).check()
            })?;
        anyhow::Ok(())
    })?;

    println!("Policy finished. Stats {}", res.stats);
    anyhow::Ok(())
}
