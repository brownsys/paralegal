extern crate anyhow;
use std::{ops::Deref, sync::Arc};

use anyhow::{bail, Result};
use clap::Parser;
use paralegal_policy::{assert_error, paralegal_spdg, Context, Diagnostics, Marker, PolicyContext};
use paralegal_spdg::{traverse::EdgeSelection, Identifier};

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

impl Deref for DeletionProp {
    type Target = PolicyContext;
    fn deref(&self) -> &Self::Target {
        self.cx.deref()
    }
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
            .iter()
            .filter(|t| {
                {
                    // If there is any controller
                    self.cx.desc().controllers.keys().any(|ctrl_id| {
                        // Where a source of that type
                        self.cx.srcs_with_type(*ctrl_id, **t).any(|sens_src| {
                            // Has data influence on
                            self.cx
                                .influencees(sens_src, EdgeSelection::Data)
                                .any(|influencee| {
                                    // A node with marker "influences"
                                    self.cx.has_marker(marker!(stores), influencee)
                                })
                        })
                    })
                }
            })
            // Mapped to their otype
            .flat_map(|t| self.cx.otypes(*t))
            .collect::<Vec<_>>();
        let found_deleter = self.cx.desc().controllers.keys().any(|ctrl_id| {
            // For all types to check
            types_to_check.iter().all(|ty| {
                // If there is any src of that type
                self.cx.srcs_with_type(*ctrl_id, **ty).any(|node| {
                    // That has data flow influence on
                    self.cx
                        .influencees(node, EdgeSelection::Data)
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
                format!("Type: {}", self.cx.describe_def(*ty))
            )
        }

        Ok(found_deleter)
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

impl Deref for ScopedStorageProp {
    type Target = PolicyContext;
    fn deref(&self) -> &Self::Target {
        self.cx.deref()
    }
}

impl ScopedStorageProp {
    pub fn new(cx: Arc<PolicyContext>) -> Self {
        ScopedStorageProp { cx }
    }

    pub fn check(self) -> Result<bool> {
        for c_id in self.cx.desc().controllers.keys() {
            // first marker used to be `scopes_store` but that one was never defined??
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
                    !(self.cx.flows_to(sens, store, EdgeSelection::Data)) || {
                        let store_callsite = self.cx.inputs_of(self.cx.associated_call_site(store));
                        // The sink that scope flows to may be another CallArgument attached to the store's CallSite, it doesn't need to be store itself.
                        let found_scope = scopes.iter().any(|scope| {
                            self.cx
                                .flows_to(*scope, &store_callsite, EdgeSelection::Data)
                                && self
                                    .cx
                                    .influencers(*scope, EdgeSelection::Data)
                                    .any(|i| self.cx.has_marker(marker!(auth_witness), i))
                        });
                        if !found_scope {
                            self.print_node_error(store, "Sensitive value store is not scoped.")
                                .unwrap();
                            self.print_node_note(sens, "Sensitive value originates here")
                                .unwrap();
                        }
                        found_scope
                    }
                })
            });

            assert_error!(
                self.cx,
                controller_valid,
                format!(
                    "Violation detected for controller: {}",
                    self.cx.desc().controllers[c_id].name
                ),
            );

            if !controller_valid {
                return Ok(controller_valid);
            }
        }
        Ok(true)
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

impl Deref for AuthDisclosureProp {
    type Target = PolicyContext;
    fn deref(&self) -> &Self::Target {
        self.cx.deref()
    }
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
                .roots(*c_id, EdgeSelection::Data)
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
                            .influencers(*node, EdgeSelection::Both)
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
                    if !self.cx.flows_to(sens, *sink, EdgeSelection::Data) {
                        continue;
                    }

                    let sink_callsite = self.cx.inputs_of(self.cx.associated_call_site(*sink));

                    // scopes for the store
                    let store_scopes = self
                        .cx
                        .influencers(&sink_callsite, EdgeSelection::Data)
                        .filter(|n| self.cx.has_marker(marker!(scopes), *n))
                        .collect::<Vec<_>>();
                    if store_scopes.is_empty() {
                        self.print_node_error(*sink, "Did not find any scopes for this sink")?;
                    }

                    // all flows are safe before scope
                    let safe_before_scope = self.cx.always_happens_before(
                        roots.iter().cloned(),
                        |n| safe_scopes.contains(&n),
                        |n| store_scopes.contains(&n),
                    )?;

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

#[derive(Parser)]
struct Args {
    /// path to WebSubmit directory.
    ws_dir: std::path::PathBuf,

    /// `edit-<property>-<articulation point>-<short edit type>`
    #[clap(long)]
    edit_type: Option<String>,

    /// sc, del, or dis.
    #[clap(long)]
    policy: Option<String>,
}

fn main() -> Result<()> {
    let args = Args::parse();

    let prop = match args.policy {
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
    command.external_annotations("baseline-external-annotations.toml");
    command.abort_after_analysis();

    if let Some(edit) = args.edit_type.as_ref() {
        command
            .get_command()
            .args(["--", "--lib", "--features", &edit]);
    }
    command.run(args.ws_dir)?.with_context(prop)?;

    Ok(())
}
