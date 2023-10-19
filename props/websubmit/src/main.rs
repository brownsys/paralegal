extern crate anyhow;
use std::sync::Arc;

use anyhow::{anyhow, Result};

use paralegal_policy::{
    assert_error, paralegal_spdg::DataSink, paralegal_spdg::Identifier, DefId, Marker,
    PolicyContext,
};

macro_rules! marker {
    ($id:ident) => {
        Marker::new_intern(stringify!($id))
    };
}

pub struct DeletionProp {
    cx: Arc<PolicyContext>,
}

impl DeletionProp {
    pub fn new(cx: Arc<PolicyContext>) -> Self {
        DeletionProp { cx }
    }

    fn flows_to_store(&self, t: DefId) -> bool {
        let stores = Marker::new_intern("stores");

        for c_id in self.cx.desc().controllers.keys() {
            let t_srcs = self.cx.srcs_with_type(*c_id, t);
            let store_cs = self
                .cx
                .all_nodes_for_ctrl(*c_id)
                .filter(|n| self.cx.has_marker(stores, *n))
                .collect::<Vec<_>>();

            for t_src in t_srcs {
                for store in &store_cs {
                    if self
                        .cx
                        .flows_to(t_src, *store, paralegal_policy::EdgeType::Data)
                    {
                        return true;
                    }
                }
            }
        }

        false
    }

    fn flows_to_deletion(&self, t: DefId) -> bool {
        let deletes = Marker::new_intern("deletes");

        let mut ots = self.cx.otypes(t);
        ots.push(t);

        for c_id in self.cx.desc().controllers.keys() {
            for ot in &ots {
                let t_srcs = self.cx.srcs_with_type(*c_id, *ot);
                let delete_cs = self
                    .cx
                    .all_nodes_for_ctrl(*c_id)
                    .filter(|n| self.cx.has_marker(deletes, *n))
                    .collect::<Vec<_>>();

                for t_src in t_srcs {
                    for delete in &delete_cs {
                        if self
                            .cx
                            .flows_to(t_src, *delete, paralegal_policy::EdgeType::Data)
                        {
                            return true;
                        }
                    }
                }
            }
        }

        false
    }

    // Asserts that there exists one controller which calls a deletion
    // function on every value (or an equivalent type) that is ever stored.
    pub fn check(self) {
        let sensitive = Marker::new_intern("sensitive");
        for (t, _) in self.cx.marked(sensitive) {
            assert_error!(
                self.cx,
                self.flows_to_store(*t) && !self.flows_to_deletion(*t),
                format!("Found an error for type: {t:?}")
            )
        }
    }
}

pub struct ScopedStorageProp {
    cx: Arc<PolicyContext>,
}

impl ScopedStorageProp {
    pub fn new(cx: Arc<PolicyContext>) -> Self {
        ScopedStorageProp { cx }
    }

    // Storing data in the database must be associated to a user. This is necessary for e.g. the deletion to work.
    pub fn check(self) {
        for (c_id, c) in &self.cx.desc().controllers {
            // TODO: scoped objects, then transform that into sources
            let scopes_srcs = self
                .cx
                .marked_sources(c, c.data_sources(), marker!(scopes))
                .collect::<Vec<_>>();
            let stores_sinks = self
                .cx
                .marked_sinks(c.data_sinks(), marker!(stores))
                .collect::<Vec<_>>();
            let sens_srcs = self
                .cx
                .marked_sources(c, c.data_sources(), marker!(sensitive))
                .collect::<Vec<_>>();

            let controller_valid = sens_srcs.iter().all(|sens| {
                stores_sinks.iter().all(|&store| {
                    !(self.cx.flows_to(
                        Some(*c_id),
                        sens,
                        &store.into(),
                        paralegal_policy::EdgeType::Data,
                    )) || (match store {
                        DataSink::Argument { function: cs, .. } => {
                            scopes_srcs.iter().any(|scope| {
                                self.cx.flows_to(
                                    Some(*c_id),
                                    scope,
                                    &cs.into(),
                                    paralegal_policy::EdgeType::Data,
                                )
                            })
                        }
                        DataSink::Return => false, // TODO: maybe can scope the return?
                    })
                })
            });

            // print!(
            //     "valid {:?}, controller {:?}, scopes_srcs {:?}, sens_srcs {:?}\n",
            //     controller_valid, c_id, scopes_srcs, sens_srcs
            // );
            assert!(controller_valid);
        }
    }
}

fn main() -> Result<()> {
    let ws_dir = std::env::args()
        .nth(1)
        .ok_or_else(|| anyhow!("expected an argument"))?;
    paralegal_policy::SPDGGenCommand::global()
        .run(ws_dir)?
        .with_context(|ctx| {
            ctx.named_policy(Identifier::new_intern("Scoped Storage Policy"), |ctx| {
                ScopedStorageProp::new(ctx).check();
                Ok(())
            })
        })
    //     .ok_or_else(|| anyhow!("expected an argument"))?;
    // paralegal_policy::SPDGGenCommand::global()
    //     .run(ws_dir)?
    //     .with_context(|ctx| {
    //         ctx.named_policy(Identifier::new_intern("Deletion Policy"), |ctx| {
    //             DeletionProp::new(ctx).check();
    //             Ok(())
    //         })
    //     })
}
