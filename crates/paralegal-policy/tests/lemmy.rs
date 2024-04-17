mod helpers;

use std::{collections::hash_map::RandomState, sync::Arc};

use helpers::{Result, Test};
use paralegal_policy::{assert_error, assert_warning, Context, Diagnostics, EdgeSelection};
use paralegal_spdg::{GlobalNode, Identifier};

const ASYNC_TRAIT_CODE: &str = stringify!(
    pub struct SaveComment {
        pub save: bool,
    }
    #[async_trait::async_trait(?Send)]
    pub trait Perform {
        type Response;

        async fn perform(&) -> Result<::Response, String>;
    }

    #[async_trait::async_trait(?Send)]
    impl Perform for SaveComment {
        type Response = ();
        #[paralegal::analyze]
        async fn perform(&) -> Result<(), String> {
            save(create().await).await;
            Ok(())
        }
    }

    #[paralegal::marker(source, return)]
    async fn create() -> usize {
        0
    }

    #[paralegal::marker(sink, arguments = [0])]
    async fn save(u: usize) {}
);

fn async_trait_policy(ctx: Arc<Context>) -> Result<()> {
    let sinks = ctx
        .marked_nodes(Identifier::new_intern("sink"))
        .collect::<Vec<_>>();
    for s in &sinks {
        ctx.node_note(*s, "Found this match for the sink marker");
    }
    assert_warning!(ctx, !sinks.is_empty(), "No sinks found");
    assert_error!(
        ctx,
        ctx.any_flows(
            &ctx.marked_nodes(Identifier::new_intern("source"))
                .collect::<Vec<_>>(),
            &sinks,
            EdgeSelection::Data
        )
        .is_some()
    );
    Ok(())
}

/// Tests we can handle `async_trait` version 0.1.53
#[test]
fn async_trait_0_1_53() -> Result<()> {
    let mut test = Test::new(ASYNC_TRAIT_CODE)?;
    test.with_dep(["async-trait@=0.1.53"]);
    test.run(async_trait_policy)
}

/// Tests we can handle whichever latest `async_trait` version cargo pulls for
/// us
#[test]
fn async_trait_latest() -> Result<()> {
    let mut test = Test::new(ASYNC_TRAIT_CODE)?;
    test.with_dep(["async-trait"]);
    test.run(async_trait_policy)
}

const CALLING_ASYNC_TRAIT_CODE: &str = stringify!(
    struct Ctx(usize, bool);

    #[paralegal::marker(source, return)]
    async fn source(_context: &Ctx) -> usize {
        0
    }

    #[paralegal::marker(sink, arguments = [0])]
    fn sink<T>(sink: T) {}

    #[paralegal::analyze]
    async fn main() {
        sink(Ctx(8, true).foo().await.unwrap())
    }

    #[async_trait::async_trait(?Send)]
    trait AsyncTrait {
        async fn foo(&) -> Result<usize, String>;
    }

    #[async_trait::async_trait(?Send)]
    impl AsyncTrait for Ctx {
        async fn foo(&) -> Result<usize, String> {
            Ok(source().await + .0)
        }
    }
);

fn calling_async_trait_policy(ctx: Arc<Context>) -> Result<()> {
    let sources = Vec::from_iter(ctx.marked_nodes(Identifier::new_intern("source")));
    let sinks = Vec::from_iter(ctx.marked_nodes(Identifier::new_intern("sink")));
    assert_error!(ctx, !sources.is_empty());
    assert_error!(ctx, !sinks.is_empty());
    assert_error!(
        ctx,
        ctx.any_flows(&sources, &sinks, EdgeSelection::Data)
            .is_some()
    );
    Ok(())
}

/// Turns out flowistry can actually handle calling async functions from
/// `async_trait` as well. So here we test that that works.
#[test]
fn support_calling_async_trait_0_1_53() -> Result<()> {
    let mut test = Test::new(CALLING_ASYNC_TRAIT_CODE)?;
    test.with_dep(["async-trait@=0.1.53"]);
    test.run(calling_async_trait_policy)
}

#[test]
fn transitive_control_flow() -> Result<()> {
    let test = Test::new(stringify!(
        use std::future::Future;
        use std::sync::Arc;

        pub struct LemmyError {
            inner: String
        }

        impl LemmyError {
            fn from_message(s: &str) -> Self {
                Self {
                    inner: s.to_owned()
                }
            }
        }

        pub struct PgConnection;

        #[derive(Clone)]
        pub struct DbPool;

        impl DbPool {
            pub fn get(&self) -> Result<Arc<PgConnection>, LemmyError> {
                Ok(Arc::new(PgConnection))
            }
        }

        pub fn block<F, R>(f: F) -> impl Future<Output = Result<R, LemmyError>>
        where
            F: FnOnce() -> R + Send + 'static,
            R: Send + 'static, {
                std::future::ready(Ok(f()))
            }

        pub async fn blocking<F, T>(pool: &DbPool, f: F) -> Result<T, LemmyError>
        where
          F: FnOnce(&PgConnection) -> T + Send + 'static,
          T: Send + 'static,
        {
          let pool = pool.clone();
          let res = block(move || {
            let conn = pool.get()?;
            let res = (f)(&conn);
            Ok(res) as Result<T, LemmyError>
          })
          .await?;

          res
        }

        #[paralegal::marker(db_access, return)]
        pub fn apply_label_read<T>(t: T) -> T { t }
        #[paralegal::marker(instance_ban_check, return)]
        pub fn apply_label_banned<T>(t: T) -> T { t }
        #[paralegal::marker(instance_delete_check, return)]
        pub fn apply_label_deleted<T>(t: T) -> T { t }
        #[paralegal::marker(db_user_read, return)]
        pub fn apply_label_user_read<T>(t: T) -> T { t }

        pub struct GetUnreadRegistrationApplicationCount {
            user_id: usize
        }

        pub struct LemmyContext {
            pool: DbPool
        }

        impl LemmyContext {
            pub fn pool(&self) -> &DbPool {
                &self.pool
            }
        }

        pub struct LocalUserView {
            person: Person
        }

        pub struct Person {
            banned: bool,
            deleted: bool,
        }

        impl LocalUserView {
            pub fn read(conn: &PgConnection, id: usize) -> Result<Self, LemmyError> {
                Ok(LocalUserView {
                    person: Person {
                        banned: false,
                        deleted: false,
                    }
                })
            }
        }

        pub struct Site {
            require_email_verification: bool
        }

        impl Site {
            pub fn read_local_site(conn: &PgConnection) -> Result<Self, LemmyError> {
                Ok(Site{ require_email_verification: true})
            }
        }
        pub struct RegistrationApplicationView {

        }

        impl RegistrationApplicationView {
            pub fn get_unread_count(conn: &PgConnection, _: bool) -> Result<usize, LemmyError> {
                Ok(0)
            }
        }

        #[paralegal::analyze]
        async fn perform(
            data: &GetUnreadRegistrationApplicationCount,
            context: &LemmyContext,
        ) -> Result<(), LemmyError> {
            let pool = context.pool();
            let local_user_id = data.user_id;
            let local_user_view = apply_label_user_read(
                blocking(pool, move |conn| LocalUserView::read(conn, local_user_id)).await??,
            );

            // Check for a site ban
            if apply_label_banned(local_user_view.person.banned) {
                return Err(LemmyError::from_message("site_ban"));
            }

            // Check for user deletion
            if apply_label_deleted(local_user_view.person.deleted) {
                return Err(LemmyError::from_message("deleted"));
            }

            let verified_email_only =
                apply_label_read(blocking(context.pool(), Site::read_local_site).await??)
                    .require_email_verification;

            let registration_applications = apply_label_read(
                blocking(context.pool(), move |conn| {
                    RegistrationApplicationView::get_unread_count(conn, verified_email_only)
                })
                .await??,
            );

            Ok(())
        }
    ))?;

    let instance_delete = Identifier::new_intern("instance_delete_check");
    let instance_ban = Identifier::new_intern("instance_ban_check");

    test.run(|ctx| {
        let accesses = ctx
            .marked_nodes(Identifier::new_intern("db_access"))
            .filter(|n| !ctx.has_marker(Identifier::new_intern("db_user_read"), *n))
            .collect::<Vec<_>>();
        println!("{} accesses total", accesses.len());
        let _delete_checks = ctx.marked_nodes(instance_delete);
        let _ban_checks = ctx.marked_nodes(instance_ban);

        let mut del_checks_found = true;

        for access in accesses {
            if !ctx
                .influencers(access, EdgeSelection::Both)
                .any(|n| ctx.has_marker(instance_delete, n))
            {
                //if !delete_checks.any(|dc| ctx.flows_to(dc, access, EdgeSelection::Both)) {
                ctx.node_error(access, "No delete check found for this access");
                del_checks_found = false;
                for i in std::collections::HashSet::<_, RandomState>::from_iter(
                    ctx.influencers(access, EdgeSelection::Both),
                ) {
                    let info = ctx.node_info(i);
                    ctx.node_note(
                        i,
                        format!("This is an influencer {} @ {}", info.description, info.at),
                    );
                }
            }
            if !ctx
                .influencers(access, EdgeSelection::Both)
                .any(|n| ctx.has_marker(instance_ban, n))
            {
                //if !ban_checks.any(|bc| ctx.flows_to(bc, access, EdgeSelection::Both)) {
                ctx.node_error(access, "No ban check found for this access");
            }
        }

        if !del_checks_found {
            let mut delete_checks = ctx.marked_nodes(instance_delete).peekable();

            if delete_checks.peek().is_none() {
                ctx.warning("No delete checks were found");
            }

            for check in delete_checks {
                let info = ctx.node_info(check);
                let mut help = ctx.struct_node_help(
                    check,
                    format!(
                        "This is an elibigle delete check {} @ {}",
                        info.description, info.at
                    ),
                );

                let influencees: Vec<GlobalNode> =
                    ctx.influencees(check, EdgeSelection::Both).collect();
                dbg!("There are {} influencees\n", influencees.len());
                for influencee in influencees {
                    // NOTE: problem is that every influencee of check_user_valid is just it
                    // so it doesn't influence the database access
                    if influencee.controller_id() == check.controller_id() {
                        continue;
                    };
                    help.with_node_note(check, "This is an influencee of the delete check");
                }
                help.emit();
            }
        }

        // if !ban_checks_found {
        //     let mut ban_checks = ctx.marked_nodes(instance_ban).peekable();

        //     if ban_checks.peek().is_none() {
        //         ctx.warning("No ban checks were found");
        //     }

        //     for check in ban_checks {
        //         let mut help = ctx.struct_node_help(check, "This is an eligible ban check");

        //         let influencees: Vec<GlobalNode> =
        //             ctx.influencees(check, EdgeSelection::Both).collect();
        //         dbg!("There are {} influencees\n", influencees.len());
        //         for influencee in influencees {
        //             if influencee.controller_id() == check.controller_id() {
        //                 continue;
        //             };
        //             help.with_node_note(check, "This is an influencee of the ban check");
        //         }
        //         help.emit();
        //     }
        // }
        Ok(())
    })
}
