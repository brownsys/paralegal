extern crate anyhow;

use anyhow::{anyhow, Result};
use std::collections::HashSet;
use std::sync::Arc;

use paralegal_policy::{
    assert_error,
    paralegal_spdg::{CallSite, Ctrl, DataSink, DataSource, Identifier},
    ControllerId, CtrlNode, Marker, PolicyContext,
};

pub struct CommunityProp {
    cx: Arc<PolicyContext>,
}

impl CommunityProp {
    pub fn new(cx: Arc<PolicyContext>) -> Self {
        CommunityProp { cx }
    }

    fn flow_to_auth(&self, sink: CtrlNode, marker: Marker) -> bool {
        let auth_nodes = self
            .cx
            .all_nodes_for_ctrl(sink.ctrl_id)
            .filter(|n| self.cx.has_marker(marker, n))
            .collect::<HashSet<_>>();

        auth_nodes.iter().any(|src| {
            self.cx
                .flows_to(src, &sink, paralegal_policy::EdgeType::Control)
        })
    }

    pub fn check(&mut self) {
        let db_community_write = Marker::new_intern("db_community_write");
        let community_delete_check = Marker::new_intern("community_delete_check");
        let community_ban_check = Marker::new_intern("community_ban_check");

        for c_id in self.cx.desc().controllers.keys() {
            for write_sink in self
                .cx
                .all_nodes_for_ctrl(c_id)
                .filter(|n| self.cx.has_marker(db_community_write, n))
            {
                let ok = self.flow_to_auth(write_sink, community_delete_check)
                    && self.flow_to_auth(write_sink, community_ban_check);
                assert_error!(self.cx, !ok, "Found a failure!");
            }
        }
    }
}

fn main() -> Result<()> {
    let lemmy_dir = std::env::args()
        .nth(1)
        .ok_or_else(|| anyhow!("expected an argument"))?;
    paralegal_policy::SPDGGenCommand::global()
        .run(lemmy_dir)?
        .with_context(|ctx| {
            ctx.named_policy(Identifier::new_intern("Community Policy"), |ctx| {
                CommunityProp::new(ctx).check();
                Ok(())
            })
        })
}
