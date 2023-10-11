extern crate anyhow;

use anyhow::{anyhow, Result};
use std::collections::HashSet;
use std::sync::Arc;

use paralegal_policy::{
    assert_error,
    paralegal_spdg::{CallSite, Ctrl, DataSink, DataSource, Identifier},
    Marker, PolicyContext,
};

pub struct CommunityProp {
    cx: Arc<PolicyContext>,
}

impl CommunityProp {
    pub fn new(cx: Arc<PolicyContext>) -> Self {
        CommunityProp { cx }
    }

    fn flow_to_auth(&self, c: &Ctrl, sink: &CallSite, marker: Marker) -> bool {
        let auth_callsites = self
            .cx
            .marked_sinks(c.data_flow.0.values().flatten(), marker)
            .filter_map(|sink| match sink {
                DataSink::Argument { function, .. } => Some(function),
                _ => None,
            })
            .collect::<HashSet<_>>();

        let mut influence_sink = c.ctrl_flow.0.iter().filter_map(|(src, dsts)| match src {
            DataSource::FunctionCall(cs) => dsts.iter().any(|dst| dst == sink).then_some(cs),
            DataSource::Argument(_) => None,
        });

        influence_sink.any(|cs| auth_callsites.contains(cs))
    }

    pub fn check(&mut self) {
        let db_community_write = Marker::new_intern("db_community_write");
        let community_delete_check = Marker::new_intern("community_delete_check");
        let community_ban_check = Marker::new_intern("community_ban_check");

        for c in self.cx.desc().controllers.values() {
            for dsts in c.data_flow.0.values() {
                for write_sink in
                    self.cx
                        .marked_sinks(dsts, db_community_write)
                        .filter_map(|sink| match sink {
                            DataSink::Argument { function, .. } => Some(function),
                            _ => None,
                        })
                {
                    let ok = self.flow_to_auth(c, write_sink, community_delete_check)
                        && self.flow_to_auth(c, write_sink, community_ban_check);
                    assert_error!(self.cx, !ok, "Found a failure!");
                }
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
