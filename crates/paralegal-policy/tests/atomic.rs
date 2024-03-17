mod helpers;

use helpers::Test;

use anyhow::Result;
use paralegal_policy::{assert_error, assert_warning, Diagnostics as _, EdgeSelection};
use paralegal_spdg::Identifier;

macro_rules! marker {
    ($name:ident) => {{
        lazy_static::lazy_static! {
            static ref MARKER: Identifier = Identifier::new_intern(stringify!($name));
        }
        *MARKER
    }};
}

#[test]
fn not_influenced_by_commit() -> Result<()> {
    let mut test = Test::new(stringify!(
        type AtomicResult<A> = Result<A, String>;
        type Value = String;

        #[derive(Clone)]
        struct Commit {
            subject: String,
            set: Option<std::collections::HashMap<String, Value>>,
            signer: String,
        }

        trait Storelike {
            #[paralegal::marker(sink, arguments = [1])]
            fn add_resource<T>(&self, t: T) -> AtomicResult<()>;

            #[paralegal::marker(resource, return)]
            fn get_resource(&self, subject: &str) -> AtomicResult<Resource>;
        }

        struct Resource {
            subject: String
        }

        #[paralegal::marker(check_rights, arguments = [1])]
        fn check_write(
            store: &impl Storelike,
            resource: &Resource,
            agent: String,
        ) -> AtomicResult<bool> {
            Ok(true)
        }

        impl Resource {
            #[paralegal::marker(new_resource, return)]
            fn set_propval(
                &mut self,
                property: String,
                value: Value,
                store: &impl Storelike
            ) -> AtomicResult<()> {
                Ok(())
            }

            fn new(subject: String) -> Self {
                Self { subject }
            }
        }

        impl Commit {
            fn into_resource(self, s: &impl Storelike) -> AtomicResult<Resource> {
                Ok(Resource { subject: self.subject })
            }

            #[paralegal::marker(safe, return)]
            fn modify_parent<T, Q>(&self, t: T, q: Q) {}

            #[paralegal::analyze]
            #[paralegal::marker(commit, arguments = [0])]
            pub fn apply_opts(
                &self,
                store: &impl Storelike,
                validate_schema: bool,
                validate_signature: bool,
                validate_timestamp: bool,
                validate_rights: bool,
            ) -> AtomicResult<Resource> {
                let commit_resource: Resource = self.clone().into_resource(store)?;
                let mut resource = match store.get_resource(&self.subject) {
                    Ok(rs) => rs,
                    Err(_) => Resource::new(self.subject.clone()),
                };
                if validate_rights {
                    self.modify_parent(&mut resource, store);
                    if !check_write(store, &resource, self.signer.clone())? {
                        return Err("".to_string());
                    }
                }
                if let Some(set) = self.set.clone() {
                    for (prop, val) in set.iter() {
                        resource.set_propval(prop.into(), val.to_owned(), store)?;
                    }
                }
                store.add_resource(&commit_resource)?;
                store.add_resource(&resource)?;
                Ok(commit_resource)
            }
        }
    ))?;

    test.run(|ctx| {
        let commits = ctx.marked_nodes(marker!(commit));
        let mut any_sink_reached = false;
        let results = commits.filter_map(|commit| {
            let check_rights = marker!(check_rights);
            // If commit is stored
            let stores = ctx.influencees(commit, EdgeSelection::Both)
                .filter(|s| ctx.has_marker(marker!(sink), *s))
                .collect::<Box<[_]>>();
            if stores.is_empty() {
                return None;
            }
            any_sink_reached = true;

            let new_resources = ctx.influencees(commit, EdgeSelection::Data)
                .filter(|n| ctx.has_marker(marker!(new_resource), *n))
                .collect::<Box<[_]>>();

            // All checks that flow from the commit but not from a new_resource
            let valid_checks = ctx.influencees(commit, EdgeSelection::Data)
                .filter(|check|
                    ctx.has_marker(check_rights, *check)
                    && new_resources.iter().all(|r| !ctx.flows_to(*r, *check, EdgeSelection::Data)))
                .collect::<Box<[_]>>();

            Some(stores.iter().copied().map(|store| {
                (store, valid_checks.iter().copied().find(|check| ctx.successors(store).any(|cs| ctx.has_ctrl_influence(*check, cs))))
            }).collect::<Box<[_]>>())
        });
        
        let likely_result = results.max_by_key(|checks| checks.iter().filter(|(_, v)| v.is_some()).count());

        if let Some(checks) = likely_result {
            for (store, check) in checks.iter().copied() {
                if let Some(check) = check {
                    let mut msg = ctx.struct_node_note(store, "This store is properly checked");
                    msg.with_node_note(check, "With this check");
                } else {
                    ctx.node_error(store, "This store is not protected");
                }
            }
        } else {
            ctx.error("No results at all. No controllers?")
        }
        assert_error!(
            ctx,
            any_sink_reached,
            "No sink was reached across controllers, the policy may be vacuous or the markers not correctly assigned/unreachable."
        );

        Ok(())
    })
}
