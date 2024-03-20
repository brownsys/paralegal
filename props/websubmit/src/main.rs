extern crate anyhow;
use std::{ops::Deref, sync::Arc};

use anyhow::{bail, Result};
use clap::Parser;
use paralegal_policy::{
    assert_error, loc, paralegal_spdg, Context, Diagnostics, IntoIterGlobalNodes, Marker,
    PolicyContext,
};
use paralegal_spdg::{traverse::EdgeSelection, GlobalNode, Identifier};

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
        let mut found_local_witnesses = true;
        for cx in self.cx.clone().controller_contexts() {
            let c_id = cx.id();
            let scopes = cx
                .all_nodes_for_ctrl(c_id)
                .filter(|node| self.cx.has_marker(marker!(scopes_store), *node))
                .collect::<Vec<GlobalNode>>();

            let stores = cx
                .all_nodes_for_ctrl(c_id)
                .filter(|node| self.cx.has_marker(marker!(stores), *node))
                .collect::<Vec<_>>();
            let mut sensitives = cx
                .all_nodes_for_ctrl(c_id)
                .filter(|node| self.cx.has_marker(marker!(sensitive), *node));

            let witness_marker = marker!(auth_witness);

            let mut witnesses = cx
                .all_nodes_for_ctrl(c_id)
                .filter(|node| self.cx.has_marker(witness_marker, *node))
                .collect::<Vec<_>>();

            let controller_valid = sensitives.all(|sens| {
                stores.iter().all(|&store| {
                    // sensitive flows to store implies some scope flows to store callsite
                    if !cx.flows_to(sens, store, EdgeSelection::Data) {
                        return true;
                    }
                    let store_callsite = cx.inputs_of(self.cx.associated_call_site(store));
                    // The sink that scope flows to may be another CallArgument attached to the store's CallSite, it doesn't need to be store itself.
                    let eligible_scopes = scopes.iter().copied().filter(|scope|
                        cx
                            .flows_to(*scope, &store_callsite, EdgeSelection::Data))
                            .collect::<Vec<_>>();
                    if eligible_scopes.iter().any(|&scope|

                            cx
                            .influencers(scope, EdgeSelection::Data)
                            .any(|i| self.cx.has_marker(witness_marker, i)))
                    {
                        return true;
                    }
                    let mut err = cx.struct_node_error(store, loc!("Sensitive value store is not scoped."));
                    err.with_node_note(sens, loc!("Sensitive value originates here"));
                    if eligible_scopes.is_empty() {
                        err.with_warning(loc!("No scopes were found to flow to this node"));
                        for &scope in &scopes {
                            err.with_node_help(scope, "This node would have been a valid scope");
                    }
                    } else {
                        for scope in eligible_scopes {
                            err.with_node_help(scope, "This scope would have been eligible but is not influenced by an `auth_whitness`");
                        }
                        if witnesses.is_empty() {
                            found_local_witnesses = false;
                            err.with_warning(format!("No local `{witness_marker}` sources found."));
                        }
                        for w in witnesses.iter().copied() {
                            err.with_node_help(w, &format!("This is a local source of `{witness_marker}`"));
                        }
                    }
                    err.emit();
                    false
                })
            });

            assert_error!(
                cx,
                controller_valid,
                format!(
                    loc!("Violation detected for controller: {}"),
                    cx.current().name
                ),
            );

            if !controller_valid {
                if scopes.is_empty() {
                    self.warning(loc!("No valid scopes were found"));
                }
                for a in cx.current().arguments().iter_global_nodes() {
                    self.note(format!("{}", cx.describe_node(a)));
                    let types = cx.current().node_types(a.local_node());
                    for t in types {
                        self.note(format!("{}", &cx.desc().type_info[&t].rendering))
                    }
                }
                return Ok(false);
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
            let mut sensitives = self
                .cx
                .all_nodes_for_ctrl(*c_id)
                .filter(|node| self.cx.has_marker(marker!(sensitive), *node));

            let some_failure = sensitives.any(|sens| {
                sinks.iter().any(|sink| {
                    // sensitive flows to store implies
                    if !self.cx.flows_to(sens, *sink, EdgeSelection::Data) {
                        return false;
                    }

                    let call_sites = self.cx.consuming_call_sites(*sink).collect::<Box<[_]>>();
                    let [cs] = call_sites.as_ref() else {
                        self.cx.node_error(
                            *sink,
                            format!(
                                "Unexpected number of call sites {} for this node",
                                call_sites.len()
                            ),
                        );
                        return false;
                    };
                    let sink_callsite = self.cx.inputs_of(*cs);

                    // scopes for the store
                    let store_scopes = self
                        .cx
                        .influencers(&sink_callsite, EdgeSelection::Data)
                        .filter(|n| self.cx.has_marker(marker!(scopes), *n))
                        .collect::<Vec<_>>();
                    if store_scopes.is_empty() {
                        self.node_error(*sink, loc!("Did not find any scopes for this sink"));
                    }

                    // all flows are safe before scope
                    let safe_before_scope = self
                        .cx
                        .always_happens_before(
                            roots.iter().cloned(),
                            |n| safe_scopes.contains(&n),
                            |n| store_scopes.contains(&n),
                        )
                        .unwrap();

                    safe_before_scope.report(self.cx.clone());

                    !safe_before_scope.holds()
                })
            });

            if some_failure {
                let mut nodes = self.marked_nodes(marker!(scopes)).peekable();
                if nodes.peek().is_none() {
                    let mut err = self.struct_help(loc!("No suitable scopes were found"));

                    for scope in nodes {
                        err.with_node_note(scope, "This location would have been a suitable scope");
                    }

                    err.emit();
                }
                return Ok(false);
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
        command.get_command().args(["--", "--features", &edit]);
    }
    let mut cfg = paralegal_policy::Config::default();
    cfg.always_happens_before_tracing = paralegal_policy::algo::ahb::TraceLevel::Full;
    let res = command
        .run(args.ws_dir)?
        .with_context_configured(cfg, prop)?;

    println!("Statistics for policy run {}", res.stats);
    assert!(res.success);

    Ok(())
}
