extern crate anyhow;

use anyhow::{anyhow, Result};
use clap::Parser;
use std::io::stdout;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, Instant};

use paralegal_policy::{
    assert_error,
    paralegal_spdg::{traverse::EdgeSelection, GlobalNode, Identifier},
    Marker, PolicyContext, Context
};

pub struct CommunityProp {
    cx: Arc<PolicyContext>,
}

impl CommunityProp {
    pub fn new(cx: Arc<PolicyContext>) -> Self {
        CommunityProp { cx }
    }

    fn flow_to_auth(&self, sink: GlobalNode, marker: Marker) -> bool {
        let mut auth_nodes = self
            .cx
            .all_nodes_for_ctrl(sink.controller_id())
            .filter(|n| self.cx.has_marker(marker, *n));

        auth_nodes.any(|src| self.cx.flows_to(src, sink, EdgeSelection::Control))
    }

    pub fn check(&mut self) {
        let db_community_write = Marker::new_intern("db_access");
        let community_delete_check = Marker::new_intern("community_delete_check");
        let community_ban_check = Marker::new_intern("community_ban_check");

        for c_id in self.cx.desc().controllers.keys() {
            for write_sink in self
                .cx
                .all_nodes_for_ctrl(*c_id)
                .filter(|n| self.cx.has_marker(db_community_write, *n))
            {
                let ok = self.flow_to_auth(write_sink, community_delete_check)
                    && self.flow_to_auth(write_sink, community_ban_check);
                assert_error!(self.cx, !ok, "Found a failure!");
            }
        }
    }
}

#[derive(Parser)]
struct Arguments {
    path: PathBuf,
    #[clap(last = true)]
    extra_args: Vec<String>,
}

fn time<T>(f: impl FnOnce() -> T) -> (T, Duration) {
    let now = Instant::now();
    let result = f();
    let elapsed = now.elapsed();
    (result, elapsed)
}

fn main() -> anyhow::Result<()> {
    let args: &'static Arguments = Box::leak(Box::new(Arguments::parse()));

    let mut cmd = paralegal_policy::SPDGGenCommand::global();
    cmd.external_annotations("external-annotations.toml");
    cmd.abort_after_analysis();
    cmd.get_command().arg("--target").arg("lemmy_api");
    cmd.get_command().args(&args.extra_args);

    let (graph, compile_time) = time(|| cmd.run(&args.path));

    let (res, policy_time) = time(|| {
        let ctx = Arc::new(graph?.build_context()?);
        let num_controllers = ctx.desc().controllers.len();
        let sum_nodes = ctx.desc().controllers.values().map(|spdg| spdg.graph.node_count()).sum::<usize>();
        println!("Analyzing over {num_controllers} controllers with avg {} nodes per graph", sum_nodes / num_controllers);
        ctx.clone().named_policy(Identifier::new_intern("Community Policy"), |ctx| {
            CommunityProp::new(ctx.clone()).check()
        });
        anyhow::Ok(ctx)
    });
    println!(
        "Policy finished. Analysis took {}, policy took {}",
        humantime::Duration::from(compile_time),
        humantime::Duration::from(policy_time)
    );
    res?.emit_diagnostics_may_exit(stdout())?;
    anyhow::Ok(())
}
