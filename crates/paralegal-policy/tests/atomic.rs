mod helpers;

use std::sync::Arc;

use helpers::Test;

use anyhow::Result;
use paralegal_policy::{assert_error, Context, Diagnostics as _, EdgeSelection};
use paralegal_spdg::Identifier;

macro_rules! marker {
    ($name:ident) => {{
        lazy_static::lazy_static! {
            static ref MARKER: Identifier = Identifier::new_intern(stringify!($name));
        }
        *MARKER
    }};
}

const ATOMIC_CODE_SHARED: &str = stringify!(
    #![allow(warnings, unused)]

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
        #[paralegal::marker(new_resource, arguments = [0])]
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
        fn modify_parent(&self, resource: &mut Resource, store: &impl Storelike) -> AtomicResult<()> {
            unimplemented!()
        }
    }
);

#[test]
fn not_influenced_by_commit() -> Result<()> {
    let mut code = ATOMIC_CODE_SHARED.to_owned();
    code.push_str(stringify!(
        impl Commit {
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
                //store.add_resource(&commit_resource)?;
                store.add_resource(&resource)?;
                Ok(commit_resource)
            }
        }
    ));
    let test = Test::new(code)?;

    test.run(atomic_policy)
}

fn atomic_policy(ctx: Arc<Context>) -> Result<()> {
    let commits = ctx.marked_nodes(marker!(commit));
    let mut any_sink_reached = false;
    let results = commits.filter_map(|commit| {
        let check_rights = marker!(check_rights);
        // If commit is stored
        let stores = ctx
            .influencees(commit, EdgeSelection::Both)
            .filter(|s| ctx.has_marker(marker!(sink), *s))
            .collect::<Box<[_]>>();
        if stores.is_empty() {
            return None;
        }
        any_sink_reached = true;

        let new_resources = ctx
            .influencees(commit, EdgeSelection::Data)
            .filter(|n| ctx.has_marker(marker!(new_resource), *n))
            .collect::<Box<[_]>>();

        for r in new_resources.iter() {
            let rs_info = ctx.node_info(*r);
            let mut msg = ctx.struct_node_help(
                *r,
                format!(
                    "This is a 'new_resource' {} @ {}",
                    rs_info.description, rs_info.at
                ),
            );
            msg.emit();
        }

        // All checks that flow from the commit but not from a new_resource
        let valid_checks = ctx
            .influencees(commit, EdgeSelection::Data)
            .filter(|check| {
                ctx.has_marker(check_rights, *check)
                    && ctx
                        .any_flows(&new_resources, &[*check], EdgeSelection::Data)
                        .is_none()
            })
            .collect::<Box<[_]>>();

        for check in ctx
            .influencees(commit, EdgeSelection::Data)
            .filter(|n| ctx.has_marker(check_rights, *n))
        {
            let check_info = ctx.node_info(check);
            let mut msg = ctx.struct_node_help(
                check,
                format!(
                    "this would be a valid check {} @ {}",
                    check_info.description, check_info.at
                ),
            );
            if let Some((from, _)) = ctx.any_flows(&new_resources, &[check], EdgeSelection::Data) {
                let new_resource_info = ctx.node_info(from);
                msg.with_node_note(
                    from,
                    format!(
                        "Influenced by this 'new_resource' {} @ {}",
                        new_resource_info.description, new_resource_info.at
                    ),
                );
            }
            msg.emit()
        }

        if valid_checks.is_empty() {
            ctx.warning("No valid checks");
        }

        Some(
            stores
                .iter()
                .copied()
                .map(|store| {
                    (
                        store,
                        valid_checks.iter().copied().find_map(|check| {
                            let store_cs = ctx
                                .successors(store)
                                .find(|cs| ctx.has_ctrl_influence(check, *cs))?;
                            Some((check, store_cs))
                        }),
                    )
                })
                .collect::<Box<[_]>>(),
        )
    });

    let likely_result =
        results.max_by_key(|checks| checks.iter().filter(|(_, v)| v.is_some()).count());

    if let Some(checks) = likely_result {
        for (store, check) in checks.iter() {
            if let Some((check, store_cs)) = check {
                let mut msg =
                    ctx.struct_node_note(*store, "This value is properly checked before storage");
                let check_info = ctx.node_info(*check);
                msg.with_node_note(
                    *check,
                    format!(
                        "Blessed by this check input {} @ {}",
                        check_info.description, check_info.at,
                    ),
                );
                msg.with_node_note(*store_cs, "At this store call site");

                msg.emit();
            } else {
                ctx.node_error(*store, "This store is not protected");
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
}

#[test]
fn policy_fail() -> Result<()> {
    let mut code = ATOMIC_CODE_SHARED.to_owned();
    code.push_str(stringify!(
        impl Commit {
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
                if let Some(set) = self.set.clone() {
                    for (prop, val) in set.iter() {
                        resource.set_propval(prop.into(), val.to_owned(), store)?;
                    }
                }
                if validate_rights {
                    self.modify_parent(&mut resource, store);
                    if !check_write(store, &resource, self.signer.clone())? {
                        return Err("".to_string());
                    }
                }
                store.add_resource(&commit_resource)?;
                //store.add_resource(&resource)?;
                Ok(commit_resource)
            }
        }
    ));
    let mut test = Test::new(code)?;

    test.expect_fail();

    test.run(atomic_policy)
}

#[test]
#[ignore = "We need to figure out if this is intended behavior."]
fn isolation() -> Result<()> {
    let test = Test::new(stringify!(
        #![allow(warnings, unused)]

        #[paralegal::marker(source, arguments = [0])]
        fn modify(_: &mut usize) {}

        #[paralegal::marker(target, arguments = [0])]
        fn modify_again(_: &mut usize) {}

        #[paralegal::analyze]
        fn main() {
            let mut source = 0;
            for _ in (0..4) {
                modify(&mut source);
            }
            modify_again(&mut source);
        }
    ))?;

    test.run(|ctx| {
        let sources = ctx
            .marked_nodes(Identifier::new_intern("source"))
            .collect::<Box<[_]>>();
        for sink in ctx.marked_nodes(Identifier::new_intern("target")) {
            let sink_info = ctx.node_info(sink);
            if let Some((from, _)) = ctx.any_flows(&sources, &[sink], EdgeSelection::Data) {
                let mut msg = ctx.struct_node_note(
                    sink,
                    format!(
                        "Sink {} @ {} is reached",
                        sink_info.description, sink_info.at
                    ),
                );
                let src_info = ctx.node_info(from);
                msg.with_node_note(
                    from,
                    format!("By this source {} @ {}", src_info.description, src_info.at),
                );
                msg.emit();
            } else {
                ctx.node_error(
                    sink,
                    format!(
                        "Sink {} @ {} is not reached by a source",
                        sink_info.description, sink_info.at
                    ),
                );
            }
        }
        Ok(())
    })
}

#[test]
fn isolation_2() -> Result<()> {
    let test = Test::new(stringify!(
        #![allow(warnings, unused)]

        struct Resource {
            subject: String,
        }

        struct Commit {
            subject: String,
        }

        impl Resource {
            fn new(subject: String) -> Self {
                Self { subject }
            }

            #[paralegal::marker(source, arguments = [0])]
            fn set_propval(&mut self) {}
        }
        impl Commit {
            #[paralegal::marker(safe, return)]
            fn modify_parent(&self, _: &mut Resource) {}
        }

        #[paralegal::marker(target, arguments = [0])]
        fn check_write(resource: &Resource) {}

        #[paralegal::analyze]
        fn main(input: &Commit) {
            let mut resource = Resource::new(input.subject.clone());

            for _ in 1..4 {
                resource.set_propval();
            }

            input.modify_parent(&mut resource);

            check_write(&resource)
        }
    ))?;

    test.run(|ctx| {
        let sources = ctx
            .marked_nodes(Identifier::new_intern("source"))
            .collect::<Box<[_]>>();
        for sink in ctx.marked_nodes(Identifier::new_intern("target")) {
            let sink_info = ctx.node_info(sink);
            if let Some((from, _)) = ctx.any_flows(&sources, &[sink], EdgeSelection::Data) {
                let mut msg = ctx.struct_node_note(
                    sink,
                    format!(
                        "Sink {} @ {} is reached",
                        sink_info.description, sink_info.at
                    ),
                );
                let src_info = ctx.node_info(from);
                msg.with_node_note(
                    from,
                    format!("By this source {} @ {}", src_info.description, src_info.at),
                );
                msg.emit();
            } else {
                ctx.node_error(
                    sink,
                    format!(
                        "Sink {} @ {} is not reached by a source",
                        sink_info.description, sink_info.at
                    ),
                );
            }
        }
        Ok(())
    })
}
