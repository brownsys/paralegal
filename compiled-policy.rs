use anyhow::Result;
use clap::{Parser, ValueEnum};
use std::sync::Arc;

use paralegal_policy::{paralegal_spdg::traverse::EdgeSelection, Context, Diagnostics, Marker};

macro_rules! marker {
    ($id:ident) => {
        Marker::new_intern(stringify!($id))
    };
}

macro_rules! policy {
    ($name:ident $(,)? $context:ident $(,)? $code:block) => {
        fn $name(ctx: Arc<Context>) -> Result<()> {
            ctx.named_policy(Identifier::new_intern(stringify!($name)), |$context| $code)
        }
    };
}

policy!(check, ctx { 
    
    let found = ctx.all_controllers().find(|(ct_id, ctrl)| {
    ctrl.name.as_str() == "user_chron_job"
    &&
    {
        let c_id = *ct_id;
        {
            let mut pageview_nodes = ctx.all_nodes_for_ctrl(c_id).filter(|n| ctx.has_marker(marker!(pageviews), *n));

            pageview_nodes.all(|pageview| {
                {
                let mut expiration_check_nodes = ctx.all_nodes_for_ctrl(c_id);

                expiration_check_nodes.any(|expiration_check| {
                    let left_3 : bool = {
                        let left_1 : bool = {
                            {
                            let mut current_time_nodes = ctx.all_nodes_for_ctrl(c_id).filter(|n| ctx.has_marker(marker!(time), *n));

                            current_time_nodes.any(|current_time| {
                                ctx.influencers(expiration_check, EdgeSelection::Data).any(|n| n == current_time)
                            })
                            }
                        };
                        let right_1 : bool = {
                            {
                                let mut fetched_pageview_date_nodes = ctx.all_nodes_for_ctrl(c_id).filter(|n| ctx.has_marker(marker!(db_access), *n));

                                fetched_pageview_date_nodes.any(|fetched_pageview_date| {
                                    let left_0 : bool = {
                                        ctx.influencers(fetched_pageview_date, EdgeSelection::Data).any(|n| n == pageview)
                                    };
                                    let right_0 : bool = {
                                        ctx.influencers(expiration_check, EdgeSelection::Data).any(|n| n == fetched_pageview_date)
                                    };
                                    left_0 && right_0
                                })
                            }
                        };
                        left_1 && right_1
                    };
                    let right_3 : bool = {
                        {
                            let mut deleter_nodes = ctx.all_nodes_for_ctrl(c_id).filter(|n| ctx.has_marker(marker!(deletes), *n));

                            deleter_nodes.any(|deleter| {
                                let left_2 : bool = {
                                    ctx.influencers(deleter, EdgeSelection::Data).any(|n| n == pageview)
                                };
                                let right_2 : bool = {
                                    ctx.has_ctrl_influence(expiration_check, deleter)
                                };
                                left_2 && right_2
                            })
                        }
                    };
                    left_3 && right_3
                })
                }
            })
        }
    }
    });

    assert_error!(ctx, found.is_some(), format!("user_chron_job does not satisfy the policy"));
    Ok(())
});

fn main() -> Result<()> {
    let dir = ".";
    let cmd = paralegal_policy::SPDGGenCommand::global();
    cmd.run(dir)?.with_context(pol)?;
    println!("Policy successful");
    Ok(())
}
