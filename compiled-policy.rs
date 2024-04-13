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
    let is_compliant = ctx.all_controllers().all(|(c_id, _ctrl)| { 
    let mut store_nodes = ctx.all_nodes_for_ctrl(c_id).filter(|n| ctx.has_marker(marker!(stores), *n));
let sensitive_store_nodes = store_nodes.filter(|n| {
    let store = *n;
    
    {
    let mut sensitive_nodes = ctx.all_nodes_for_ctrl(c_id).filter(|n| ctx.has_marker(marker!(sensitive), *n));

    sensitive_nodes
    .any(|sensitive| {
        ctx.influencers(store, EdgeSelection::Data).any(|n| n == sensitive)
    })
}
    
}).collect::<Vec<_>>();

    {
    

    sensitive_store_nodes
    .clone().into_iter()
    .all(|sensitive_store| {
        {
    let mut scope_nodes = ctx.all_nodes_for_ctrl(c_id).filter(|n| ctx.has_marker(marker!(scopes_store), *n));

    scope_nodes
    .any(|scope| {
        let left_0 : bool = {
    {
    let mut authorization_nodes = ctx.all_nodes_for_ctrl(c_id).filter(|n| ctx.has_marker(marker!(auth_witness), *n));

    authorization_nodes
    .any(|authorization| {
        ctx.influencers(scope, EdgeSelection::Data).any(|n| n == authorization)
    })
}
};
let right_0 : bool = {
    {
let sensitive_store_callsite = ctx.inputs_of(ctx.associated_call_site(sensitive_store));
ctx.flows_to(scope, &sensitive_store_callsite, EdgeSelection::Data)
}
};
left_0 && right_0
    })
}
    })
}
});
    assert_error!(ctx, is_compliant, format!("At least one controller does not satisfy the policy"));
    Ok(())
});

fn main() -> Result<()> {
    let dir = ".";
    let cmd = paralegal_policy::SPDGGenCommand::global();
    cmd.run(dir)?.with_context(pol)?;
    println!("Policy successful");
    Ok(())
}
