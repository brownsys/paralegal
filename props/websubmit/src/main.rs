extern crate anyhow;
use std::sync::Arc;

use anyhow::{anyhow, bail, Result};

use paralegal_policy::{assert_error, paralegal_spdg::Identifier, Context, Marker, PolicyContext};

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

    pub fn check(self) {
        // All types marked "sensitive"
        let types_to_check = self
            .cx
            .marked_type(marker!(sensitive))
            .filter(|t| {
                {
                    // If there is any controller
                    self.cx.desc().controllers.keys().any(|ctrl_id| {
                        // Where a source of that type
                        self.cx.srcs_with_type(*ctrl_id, *t).any(|sens_src| {
                            // Has data influence on
                            self.cx
                                .influencees(sens_src, paralegal_policy::EdgeType::Data)
                                .any(|influencee| {
                                    // A node with marker "influences"
                                    self.cx.has_marker(marker!(stores), influencee)
                                })
                        })
                    })
                }
            })
            // Mapped to their otype
            .flat_map(|t| self.cx.otypes(t))
            .collect::<Vec<_>>();
        let found_deleter = self.cx.desc().controllers.keys().any(|ctrl_id| {
            // For all types to check
            types_to_check.iter().all(|ty| {
                // If there is any src of that type
                self.cx.srcs_with_type(*ctrl_id, *ty).any(|node| {
                    // That has data flow influence on
                    self.cx
                        .influencees(node, paralegal_policy::EdgeType::Data)
                        // A node with marker "deletes"
                        .any(|influencee| self.cx.has_marker(marker!(deletes), influencee))
                })
            })
        });

        assert_error!(
            self.cx,
            found_deleter,
            format!("No valid deleter found for all types: {:?}", types_to_check),
        );
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
