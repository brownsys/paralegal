#![feature(rustc_private)]

mod helpers;

use std::{collections::HashSet, sync::Arc};

use helpers::Test;

use anyhow::Result;
use paralegal_policy::{
    assert_error, Context, Diagnostics as _, EdgeSelection, NodeExt as _, RootContext,
};
use paralegal_spdg::{Identifier, NodeCluster};

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

fn atomic_policy(ctx: Arc<RootContext>) -> Result<()> {
    let mut any_sink_reached = false;
    let check_rights = marker!(check_rights);
    for ctx in ctx.controller_contexts() {
        let commit = NodeCluster::new(
            ctx.id(),
            ctx.marked_nodes(marker!(commit))
                .filter(|n| n.controller_id() == ctx.id())
                .map(|n| n.local_node()),
        );

        // If commit is stored
        let stores = ctx
            .influencees(&commit, EdgeSelection::Both)
            .filter(|s| s.has_marker(&ctx, marker!(sink)))
            .collect::<Box<[_]>>();
        if stores.is_empty() {
            continue;
        }
        any_sink_reached = true;

        let new_resources = ctx
            .influencees(&commit, EdgeSelection::Data)
            .filter(|n| n.has_marker(&ctx, marker!(new_resource)))
            .collect::<Box<[_]>>();

        for r in new_resources.iter() {
            let rs_info = r.info(&ctx);
            let msg = ctx.struct_node_help(
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
            .influencees(&commit, EdgeSelection::Data)
            .filter(|check| {
                check.has_marker(&ctx, check_rights)
                    && ctx
                        .any_flows(&new_resources, &[*check], EdgeSelection::Data)
                        .is_none()
            })
            .collect::<Box<[_]>>();

        for check in ctx
            .influencees(&commit, EdgeSelection::Data)
            .filter(|n| n.has_marker(&ctx, check_rights))
        {
            let check_info = check.info(&ctx);
            let mut msg = ctx.struct_node_help(
                check,
                format!(
                    "this would be a valid check {} @ {}",
                    check_info.description, check_info.at
                ),
            );
            if let Some((from, _)) = ctx.any_flows(&new_resources, &[check], EdgeSelection::Data) {
                let new_resource_info = from.info(&ctx);
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

        let checks = stores
            .iter()
            .copied()
            .map(|store| {
                (
                    store,
                    valid_checks.iter().copied().find_map(|check| {
                        let store_cs = store
                            .successors(&ctx)
                            .find(|cs| ctx.has_ctrl_influence(check, *cs))?;
                        Some((check, store_cs))
                    }),
                )
            })
            .collect::<Box<[_]>>();

        for (store, check) in checks.iter() {
            if let Some((check, store_cs)) = check {
                let mut msg =
                    ctx.struct_node_note(*store, "This value is properly checked before storage");
                let check_info = check.info(&ctx);
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
                store.add_resource(&resource)?;
                Ok(commit_resource)
            }
        }
    ));
    let mut test = Test::new(code)?;

    test.expect_fail();

    test.run(atomic_policy)
}

#[test]
fn isolation_3() -> Result<()> {
    let mut code = ATOMIC_CODE_SHARED.to_owned();
    code.push_str(stringify!(
        impl Commit {
            #[paralegal::analyze]
            #[paralegal::marker(commit, arguments = [0])]
            pub fn apply_opts(
                &self,
                store: &impl Storelike,
            ) -> AtomicResult<Resource> {
                let commit_resource: Resource = self.clone().into_resource(store)?;
                let mut resource =
                    Resource::new(self.subject.clone());
                if let Some(set) = self.set.clone() {
                    for (prop, val) in set.iter() {
                        resource.set_propval(prop.into(), val.to_owned(), store)?;
                    }
                }
                self.modify_parent(&mut resource, store);
                if !check_write(store, &resource, self.signer.clone())? {
                    return Err("".to_string());
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
            let sink_info = sink.info(&ctx);
            if let Some((from, _)) = ctx.any_flows(&sources, &[sink], EdgeSelection::Data) {
                let mut msg = ctx.struct_node_note(
                    sink,
                    format!(
                        "Sink {} @ {} is reached",
                        sink_info.description, sink_info.at
                    ),
                );
                let src_info = from.info(&ctx);
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
            let sink_info = sink.info(&ctx);
            if let Some((from, _)) = ctx.any_flows(&sources, &[sink], EdgeSelection::Data) {
                let mut msg = ctx.struct_node_note(
                    sink,
                    format!(
                        "Sink {} @ {} is reached",
                        sink_info.description, sink_info.at
                    ),
                );
                let src_info = from.info(&ctx);
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
fn commit_e5cca39440ad34ee6dc2ca0aebd16ceabb3abcd6() -> Result<()> {
    let test = Test::new(stringify!(

        #![allow(warnings, unused)]

        mod urls {
            pub const PARENT: &str = "";
        }

        type AtomicResult<A> = Result<A, String>;
        type Value = String;

        #[derive(Clone)]
        struct Commit {
            subject: String,
            set: Option<std::collections::HashMap<String, Value>>,
            signer: String,
            destroy: Option<bool>,
        }

        trait Storelike {
            #[paralegal::marker(sink, arguments = [1])]
            fn add_resource_opts(
                &self,
                resource: &Resource,
                check_required_props: bool,
                update_index: bool,
                overwrite_existing: bool,
            ) -> AtomicResult<()>;

            #[paralegal::marker(resource, return)]
            fn get_resource(&self, subject: &str) -> AtomicResult<Resource>;
            fn add_atom_to_index(&self, _atom: &Atom) -> AtomicResult<()> {
                Ok(())
            }
            fn remove_atom_from_index(&self, _atom: &Atom) -> AtomicResult<()> {
                Ok(())
            }
            fn get_self_url(&self) -> Option<String> {
                None
            }
        }

        #[derive(Clone)]
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
            #[paralegal::marker(noinline)]
            pub fn get(&self, property_url: &str) -> AtomicResult<&Value> {
                unimplemented!()
            }
            pub fn get_subject(&self) -> &String {
                &self.subject
            }
        }
        pub struct Atom {
            /// The URL where the resource is located
            pub subject: String,
            pub property: String,
            pub value: Value,
        }

        impl Atom {
            pub fn new(subject: String, property: String, value: Value) -> Self {
                Atom {
                    subject,
                    property,
                    value,
                }
            }
        }

        impl Commit {
            #[paralegal::marker(resource, return)]
            fn into_resource(self, s: &impl Storelike) -> AtomicResult<Resource> {
                Ok(Resource { subject: self.subject })
            }

            #[paralegal::analyze]
            #[paralegal::marker(commit, arguments = [0])]
            fn apply_opts(
                &self,
                store: &impl Storelike,
                //validate_schema: bool,
                // validate_signature: bool,
                // validate_timestamp: bool,
                validate_rights: bool,
                update_index: bool,
            ) -> AtomicResult<()> {
                // let subject_url =
                //     url::Url::parse(&self.subject).map_err(|e| format!("Subject is not a URL. {}", e))?;
                // if subject_url.query().is_some() {
                //     return Err("Subject URL cannot have query parameters".into());
                // }

                // if validate_signature {
                //     let signature = match self.signature.as_ref() {
                //         Some(sig) => sig,
                //         None => return Err("No signature set".into()),
                //     };
                //     // TODO: Check if commit.agent has the rights to update the resource
                //     let pubkey_b64 = store
                //         .get_resource(&self.signer)?
                //         .get(urls::PUBLIC_KEY)?
                //         .to_string();
                //     let agent_pubkey = base64::decode(pubkey_b64)?;
                //     let stringified_commit = self.serialize_deterministically_json_ad(store)?;
                //     let peer_public_key =
                //         ring::signature::UnparsedPublicKey::new(&ring::signature::ED25519, agent_pubkey);
                //     let signature_bytes = base64::decode(signature.clone())?;
                //     peer_public_key
                //         .verify(stringified_commit.as_bytes(), &signature_bytes)
                //         .map_err(|_e| {
                //             format!(
                //                 "Incorrect signature for Commit. This could be due to an error during signing or serialization of the commit. Compare this to the serialized commit in the client: {}",
                //                 stringified_commit,
                //             )
                //         })?;
                // }
                // Check if the created_at lies in the past
                // if validate_timestamp {
                //     check_timestamp(self.created_at)?;
                // }
                let commit_resource: Resource = Resource { subject: self.subject.clone() };
                // Create a new resource if it doens't exist yet
                // let mut resource_old = match store.get_resource(&self.subject) {
                //     Ok(rs) => rs,
                //     Err(_) => {
                //         is_new = true;
                //         Resource::new(self.subject.clone())
                //     }
                // };

                let mut resource_old = Resource::new(self.subject.clone());
                let is_new = true;

                let resource_new = self.apply_changes(resource_old.clone(), store /* , false */)?;

                if validate_rights {
                    // if is_new {
                    //     if !check_write(store, &resource_new, self.signer.clone())? {
                    //         return Err("".to_string());
                    //     }
                    // } else {
                        // Set a parent only if the rights checks are to be validated.
                        // If there is no explicit parent set on the previous resource, use a default.
                        // Unless it's a Drive!
                        // This should use the _old_ resource, no the new one, as the new one might maliciously give itself write rights.
                        if !check_write(store, &resource_old, self.signer.clone())? {
                            return Err("".to_string());
                        }
                    // }
                };
                // Check if all required props are there
                // if validate_schema {
                //     resource_new.check_required_props(store)?;
                // }
                // If a Destroy field is found, remove the resource and return early
                // TODO: Should we remove the existing commits too? Probably.
                if let Some(destroy) = self.destroy {
                    if destroy {
                        // Note: the value index is updated before this action, in resource.apply_changes()
                        //store.remove_resource(&self.subject)?;
                        store.add_resource_opts(&commit_resource, false, update_index, false )?;
                        return Ok(());
                    }
                }
                //self.apply_changes(resource_old.clone(), store, update_index)?;

                //store.add_resource_opts(&commit_resource, false, update_index, false )?;
                Ok(())
            }
            pub fn apply_changes(
                &self,
                mut resource: Resource,
                store: &impl Storelike,
                //update_index: bool,
            ) -> AtomicResult<Resource> {
                if let Some(set) = self.set.clone() {
                    for (prop, val) in set.iter() {
                        // if update_index {
                        //     let atom = Atom::new(resource.get_subject().clone(), prop.into(), val.clone());
                        //     if let Ok(_v) = resource.get(prop) {
                        //         store.remove_atom_from_index(&atom)?;
                        //     }
                        //     store.add_atom_to_index(&atom)?;
                        // }
                        resource.set_propval(prop.into(), val.to_owned(), store)?;
                    }
                }
                // if let Some(remove) = self.remove.clone() {
                //     for prop in remove.iter() {
                //         if update_index {
                //             let val = resource.get(prop)?;
                //             let atom = Atom::new(resource.get_subject().clone(), prop.into(), val.clone());
                //             store.remove_atom_from_index(&atom)?;
                //         }
                //         resource.remove_propval(prop);
                //     }
                // }
                // Remove all atoms from index if destroy
                // if let Some(destroy) = self.destroy {
                //     if destroy {
                //         for atom in resource.to_atoms()?.iter() {
                //             store.remove_atom_from_index(atom)?;
                //         }
                //     }
                // }
                Ok(resource)
            }
        }
    ))?;

    test.run(|ctx| {
        let mut any_sink_reached = false;
        let check_rights = marker!(check_rights);
        for ctx in ctx.controller_contexts() {
            let commit = NodeCluster::new(
                ctx.id(),
                ctx.marked_nodes(marker!(commit))
                    .filter(|n| n.controller_id() == ctx.id())
                    .map(|n| n.local_node()),
            );

            // If commit is stored
            let stores = ctx
                .influencees(&commit, EdgeSelection::Both)
                .filter(|s| s.has_marker(&ctx, marker!(sink)))
                .collect::<Box<[_]>>();
            if stores.is_empty() {
                continue;
            }
            any_sink_reached = true;

            let commit_influencees = ctx.influencees(&commit, EdgeSelection::Data).collect::<HashSet<_>>();

            // All checks that flow from the commit but not from a new_resource
            let valid_checks = commit_influencees.iter().copied()
                .filter(|check| {
                    check.has_marker(&ctx, check_rights)
                })
                .collect::<Box<[_]>>();

            if valid_checks.is_empty() {
                ctx.warning("No valid checks");
            }

            let checks = stores
                .iter()
                .copied()
                .map(|store| {
                    (
                        store,
                        valid_checks.iter().copied().find_map(|check| {
                            let store_cs = store
                                .successors(&ctx)
                                .find(|cs| ctx.has_ctrl_influence(check, *cs))?;
                            Some((check, store_cs))
                        }),
                    )
                })
                .collect::<Box<[_]>>();

            for (store, check) in checks.iter() {
                if check.is_none() {
                    let store_influencing = ctx.influencers(*store, EdgeSelection::Control).chain(
                        ctx.influencers(*store, EdgeSelection::Control).flat_map(|i| ctx.influencers(i, EdgeSelection::Data))
                    ).collect::<HashSet<_>>();

                    ctx.node_error(*store, "This store is not protected");

                    let mut msg = ctx.struct_node_help(*store, "This store");
                    for influencer in store_influencing.iter().copied() {
                        msg.with_node_note(influencer, "Is ctrl-influenced by this");
                    }
                    msg.emit();
                    for c in valid_checks.iter().copied() {
                        let mut msg = ctx.struct_node_help(c, "This is a valid check");

                        let check_influenced =
                            ctx.influencees(c, EdgeSelection::Control).chain(
                                ctx.influencees(c, EdgeSelection::Data).flat_map(|i| ctx.influencees(i, EdgeSelection::Control))
                            ).collect::<HashSet<_>>();
                        for i in check_influenced.iter().copied() {
                            msg.with_node_note(i, "that ctrl-influences this node");
                        }
                        msg.emit();

                        for i in store_influencing.intersection(&check_influenced) {
                            ctx.node_help(*i, "This is where influence intersects");
                        }

                        for i in store_influencing.iter().copied() {
                            let mut msg = ctx.struct_node_help(i, "This store influence intersects");
                            let mut emit = false;
                            for intersection in ctx.influencers(i, EdgeSelection::Data) {
                                if check_influenced.contains(&intersection) {
                                    msg.with_node_note(intersection, "via this intermediary");
                                    emit = true;
                                }
                            }
                            if emit {
                                msg.emit();
                            }
                        }

                        if ctx.influencees(c, EdgeSelection::Both).any(|i| i == *store) {
                            ctx.help("It reaches somehow");
                        } else {
                            ctx.warning("It never reaches.");
                        }

                    }
                }
            }
        }
        assert_error!(
            ctx,
            any_sink_reached,
            "No sink was reached across controllers, the policy may be vacuous or the markers not correctly assigned/unreachable."
        );

        Ok(())
    })
}

#[test]
fn tiny_commit_e5cca39440ad34ee6dc2ca0aebd16ceabb3abcd6() -> Result<()> {
    Test::new(stringify!(
        #[paralegal::marker(a, return)]
        fn source() -> bool {
            true
        }

        #[paralegal::marker(b, arguments = [0])]
        fn target(i: usize) {}

        #[paralegal::analyze]
        fn main() {
            let deter = Some(false);
            let src = 0;
            if source() {
                return;
            }
            if let Some(b) = deter {
                if b {
                    target(src);
                }
            }
        }
    ))?
    .run(|ctx| {
        assert_error!(
            ctx,
            ctx.marked_nodes(Identifier::new_intern("a"))
                .flat_map(|n| ctx.influencees(n, EdgeSelection::Both))
                .any(|n| n.has_marker(&ctx, Identifier::new_intern("b")))
        );
        Ok(())
    })
}
