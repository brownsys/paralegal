extern crate anyhow;
use std::sync::Arc;

use anyhow::{anyhow, bail, Result};

use paralegal_policy::{
    assert_error, paralegal_spdg::Identifier, Context, DefId, Marker, PolicyContext,
};

macro_rules! marker {
    ($id:ident) => {
        Marker::new_intern(stringify!($id))
    };
}

/// Asserts that there exists one controller which calls a deletion
/// function on every value (or an equivalent type) that is ever stored.
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

fn run_del_policy(ctx: Arc<Context>) -> Result<()> {
    ctx.named_policy(Identifier::new_intern("Deletion"), |ctx| {
        DeletionProp::new(ctx).check();
        Ok(())
    })
}

/// Storing data in the database must be associated to a user. This is
/// necessary for e.g. the deletion to work.
pub struct ScopedStorageProp {
    cx: Arc<PolicyContext>,
}

impl ScopedStorageProp {
    pub fn new(cx: Arc<PolicyContext>) -> Self {
        ScopedStorageProp { cx }
    }

    pub fn check(self) {
        for c_id in self.cx.desc().controllers.keys() {
            let scopes = self
                .cx
                .all_nodes_for_ctrl(*c_id)
                .filter(|node| self.cx.has_marker(marker!(scopes), *node))
                .collect::<Vec<_>>();
            let stores = self
                .cx
                .all_nodes_for_ctrl(*c_id)
                .filter(|node| self.cx.has_marker(marker!(stores), *node))
                .collect::<Vec<_>>();
            let mut sensitives = self
                .cx
                .all_nodes_for_ctrl(*c_id)
                .filter(|node| self.cx.has_marker(marker!(sensitive), *node));

            let controller_valid = sensitives.all(|sens| {
                stores.iter().all(|&store| {
                    // sensitive flows to store implies some scope flows to store callsite
                    !(self
                        .cx
                        .flows_to(sens, store, paralegal_policy::EdgeType::Data))
                        ||
						// The sink that scope flows to may be another CallArgument attached to the store's CallSite, it doesn't need to be store itself.
						store.associated_call_site().is_some_and(|store_callsite| {
                            let found_scope = scopes.iter().any(|scope| {
                                self.cx.flows_to(
                                    *scope,
                                    store_callsite,
                                    paralegal_policy::EdgeType::Data,
                                )
                            });
                            assert_error!(
                                self.cx,
                                found_scope,
                                format!(
                                    "Stored sensitive isn't scoped. sensitive {} stored here: {}",
                                    self.cx.describe_node(sens),
                                    self.cx.describe_node(store)
                                )
                            );
                            found_scope
                        })
                })
            });

            assert_error!(
                self.cx,
                controller_valid,
                format!(
                    "Violation detected for controller: {}",
                    self.cx.describe_def(*c_id)
                ),
            );
        }
    }
}

fn run_sc_policy(ctx: Arc<Context>) -> Result<()> {
    ctx.named_policy(Identifier::new_intern("Scoped Storage"), |ctx| {
        ScopedStorageProp::new(ctx).check();
        Ok(())
    })
}

fn main() -> Result<()> {
    let ws_dir = std::env::args()
        .nth(1)
        .ok_or_else(|| anyhow!("expected format: cargo run <path> [policy]"))?;
    let prop_name = std::env::args().nth(2);

    let prop = match prop_name {
        Some(s) => match s.as_str() {
            "sc" => run_sc_policy,
            "del" => run_del_policy,
            other => bail!("don't recognize the property name '{other}'"),
        },
        None => |ctx: Arc<Context>| run_sc_policy(ctx.clone()).and(run_del_policy(ctx)),
    };

    paralegal_policy::SPDGGenCommand::global()
        .run(ws_dir)?
        .with_context(prop)
}
