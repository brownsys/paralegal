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

    pub fn check(self) -> Result<bool> {
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
            "Did not find valid deleter for all types."
        );
        for ty in types_to_check {
            assert_error!(
                self.cx,
                found_deleter,
                format!("Type: {}", self.cx.describe_def(ty))
            )
        }

        return Ok(found_deleter);
    }
}

pub fn run_del_policy(ctx: Arc<Context>) -> Result<bool> {
    ctx.named_policy(Identifier::new_intern("Deletion"), |ctx| {
        DeletionProp::new(ctx).check()
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

    pub fn check(self) -> Result<bool> {
        for c_id in self.cx.desc().controllers.keys() {
            let scopes = self
                .cx
                .all_nodes_for_ctrl(*c_id)
                .filter(|node| self.cx.has_marker(marker!(scopes_store), *node))
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
                                ) && 
								self.cx.influencers(
									*scope, 
									paralegal_policy::EdgeType::Data
								).any(|i| self.cx.has_marker(marker!(auth_witness), i))
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

            if !controller_valid {
                return Ok(controller_valid);
            }
        }
        return Ok(true);
    }
}

pub fn run_sc_policy(ctx: Arc<Context>) -> Result<bool> {
    ctx.named_policy(Identifier::new_intern("Scoped Storage"), |ctx| {
        ScopedStorageProp::new(ctx).check()
    })
}

/// If sensitive data is released, the release must be scoped, and all inputs to the scope must be safe.
pub struct AuthDisclosureProp {
    cx: Arc<PolicyContext>,
}

impl AuthDisclosureProp {
    pub fn new(cx: Arc<PolicyContext>) -> Self {
        AuthDisclosureProp { cx }
    }

    pub fn check(self) -> Result<bool> {
        for c_id in self.cx.desc().controllers.keys() {
            // All srcs that have no influencers
            let roots = self
                .cx
                .roots(*c_id, paralegal_policy::EdgeType::Data)
                .collect::<Vec<_>>();

            let safe_scopes = self
                .cx
                // All nodes marked "safe"
                .all_nodes_for_ctrl(*c_id)
                .filter(|n| self.cx.has_marker(marker!(safe_source), *n))
                // And all nodes marked "safe_with_bless"
                .chain(self.cx.all_nodes_for_ctrl(*c_id).filter(|node| {
                    self.cx.has_marker(marker!(safe_source_with_bless), *node)
                        && self
                            .cx
                            // That are influenced by a node marked "bless"
                            .influencers(*node, paralegal_policy::EdgeType::DataAndControl)
                            .any(|b| self.cx.has_marker(marker!(bless_safe_source), b))
                }))
                .collect::<Vec<_>>();
            let sinks = self
                .cx
                .all_nodes_for_ctrl(*c_id)
                .filter(|n| self.cx.has_marker(marker!(sink), *n))
                .collect::<Vec<_>>();
            let sensitives = self
                .cx
                .all_nodes_for_ctrl(*c_id)
                .filter(|node| self.cx.has_marker(marker!(sensitive), *node));

            for sens in sensitives {
                for sink in sinks.iter() {
                    // sensitive flows to store implies
                    if !self
                        .cx
                        .flows_to(sens, *sink, paralegal_policy::EdgeType::Data)
                    {
                        continue;
                    }

                    let Some(sink_callsite) = sink.associated_call_site() else {
                        assert_error!(
                            self.cx,
                            false,
                            format!(
                                "sink {} does not have associated callsite",
                                self.cx.describe_node(*sink)
                            )
                        );
                        continue;
                    };

                    // scopes for the store
                    let store_scopes = self
                        .cx
                        .influencers(sink_callsite, paralegal_policy::EdgeType::Data)
                        .filter(|n| self.cx.has_marker(marker!(scopes), *n))
                        .collect::<Vec<_>>();
                    assert_error!(
                        self.cx,
                        !store_scopes.is_empty(),
                        format!(
                            "Did not find any scopes for sink {}",
                            self.cx.describe_node(*sink)
                        )
                    );

                    // all flows are safe before scope
                    let safe_before_scope = self.cx.always_happens_before(
                        roots.iter().cloned(),
                        |n| safe_scopes.contains(&n),
                        |n| store_scopes.contains(&n),
                    )?;

                    assert_error!(
                        self.cx,
                        safe_before_scope.holds(),
                        format!(
                            "Sensitive {} flowed to sink {} which did not have safe scopes",
                            self.cx.describe_node(sens),
                            self.cx.describe_node(*sink),
                        )
                    );
                    safe_before_scope.report(self.cx.clone());

                    if !safe_before_scope.holds() {
                        return Ok(false);
                    }
                }
            }
        }
        Ok(true)
    }
}

pub fn run_dis_policy(ctx: Arc<Context>) -> Result<bool> {
    ctx.named_policy(Identifier::new_intern("Authorized Disclosure"), |ctx| {
        AuthDisclosureProp::new(ctx).check()
    })
}

fn main() -> Result<()> {
    let ws_dir = std::env::args()
        .nth(1)
        .ok_or_else(|| anyhow!("expected format: cargo run <path> [edit-<property>-<articulation point>-<short edit type> | none] [policy]"))?;
    let edit_name = std::env::args().nth(2);
    let prop_name = std::env::args().nth(3);

    let prop = match prop_name {
        Some(s) => match s.as_str() {
            "sc" => run_sc_policy,
            "del" => run_del_policy,
            "dis" => run_dis_policy,
            other => bail!("don't recognize the property name '{other}'"),
        },
        None => |ctx: Arc<Context>| {
            run_dis_policy(ctx.clone()).and(run_sc_policy(ctx.clone()).and(run_del_policy(ctx)))
        },
    };

    let mut command = paralegal_policy::SPDGGenCommand::global();
	command.get_command().args([
		"--model-version",
		"v2",
		"--inline-elision",
		"--skip-sigs",
		"--abort-after-analysis",
		"--external-annotations",
		format!("{}baseline-external-annotations.toml", ws_dir).as_str(),
	]);

    match edit_name {
        Some(edit) => {
			if edit.as_str() != "none" {
				command.get_command().args(["--", "--features", &edit]);
			}
        }
        None => (),
    }
    command.run(ws_dir)?.with_context(prop)?;

    return Ok(());
}
