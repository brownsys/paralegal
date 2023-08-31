#![feature(rustc_private)]

use std::{collections::HashSet, sync::Arc};

use dfcheck::{
  context::{Context, Label},
  dfpp::desc::{CallSite, Ctrl, DataSource},
};

pub struct CommunityProp {
  cx: Arc<Context>,
}

impl CommunityProp {
  pub fn new(cx: Arc<Context>) -> Self {
    CommunityProp { cx }
  }

  fn flow_to_auth(&self, c: &Ctrl, sink: &CallSite, label: Label) -> bool {
    let auth_callsites = self
      .cx
      .labeled_callsites(c.data_flow.0.values().flatten(), label)
      .collect::<HashSet<_>>();

    let influence_sink = c.ctrl_flow.0.iter().filter_map(|(src, dsts)| match src {
      DataSource::FunctionCall(cs) => dsts.iter().any(|dst| dst == sink).then_some(cs),
      DataSource::Argument(_) => None,
    });

    influence_sink
      .filter(|cs| auth_callsites.contains(cs))
      .next()
      .is_some()
  }

  pub fn check(&self) {
    let db_community_write = Label::intern("db_community_write");
    let community_delete_check = Label::intern("community_delete_check");
    let community_ban_check = Label::intern("community_ban_check");

    for (_cid, c) in &self.cx.desc().controllers {
      for (_src, dsts) in &c.data_flow.0 {
        for write_sink in self.cx.labeled_callsites(dsts, db_community_write) {
          let ok = self.flow_to_auth(c, write_sink, community_delete_check)
            && self.flow_to_auth(c, write_sink, community_ban_check);
          if !ok {
            println!("Found an failure!");
          }
        }
      }
    }
  }
}

#[no_mangle]
pub fn run(cx: Arc<Context>) {
    CommunityProp::new(cx).check();
}