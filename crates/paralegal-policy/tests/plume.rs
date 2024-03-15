mod helpers;

use helpers::Test;

use anyhow::Result;

use paralegal_policy::{Diagnostics, EdgeSelection};
use paralegal_spdg::Identifier;

macro_rules! marker {
    ($id:ident) => {
        Identifier::new_intern(stringify!($id))
    };
}

#[test]
fn notification_deletion() -> Result<()> {
    let test = Test::new(stringify!(
        type Result<A> = std::result::Result<A, String>;
        #[paralegal::marker(deletes, arguments = [0])]
        fn diesel_delete<T>(t: T) -> Result<()> {
            unimplemented!()
        }

        #[paralegal::marker(user_data)]
        pub struct Notification {}

        pub struct User {}

        pub struct Connection {}

        impl User {
            #[paralegal::analyze]
            pub fn delete(&self, conn: &Connection) -> Result<()> {
                for notif in Notification::find_followed_by(conn, self)? {
                    notif.delete(conn)?
                }
                Ok(())
            }
        }

        impl Notification {
            pub fn delete(&self, conn: &Connection) -> Result<()> {
                diesel_delete(self)
                // diesel::delete(self)
                //     .execute(conn)
                //     .map(|_| ())
                //     .map_err(Error::from)
            }
            #[paralegal_flow::marker(noinline, arguments = [0])]
            pub fn find_followed_by(conn: &Connection, user: &User) -> Result<Vec<Notification>> {
                unimplemented!()
            }
        }
    ))?;

    test.run(|ctx| {
        let user_data_types = ctx.marked_type(marker!(user_data));

        let found = ctx.all_controllers().find(|(deleter_id, ctrl)| {
            let delete_sinks = ctx
                .all_nodes_for_ctrl(*deleter_id)
                .filter(|n| ctx.has_marker(marker!(to_delete), *n))
                .collect::<Vec<_>>();
            user_data_types.iter().all(|&t| {
                let sources = ctx.srcs_with_type(*deleter_id, t).collect::<Vec<_>>();
                if ctx
                    .any_flows(&sources, &delete_sinks, EdgeSelection::Data)
                    .is_none()
                {
                    let mut note = ctx.struct_note(format!(
                        "The type {} is not being deleted in {}",
                        ctx.desc().def_info[&t].name,
                        ctrl.name
                    ));
                    for src in sources {
                        note.with_node_note(src, "This is a source for that type");
                    }
                    for snk in &delete_sinks {
                        note.with_node_note(*snk, "This is a potential delete sink");
                    }
                    note.emit();
                    false
                } else {
                    true
                }
            })
        });
        if found.is_none() {
            ctx.error("Could not find a function deleting all types");
        }
        if let Some((found, _)) = found {
            println!(
                "Found {} deletes all user data types",
                ctx.desc().controllers[&found].name
            );
            for t in user_data_types {
                println!("Found user data {}", ctx.describe_def(*t));
            }
        }
        Ok(())
    })
}
