use crate::Context;
use crate::ControllerId;
use paralegal_flow::test_utils::PreFrg;
use paralegal_spdg::IntoIterGlobalNodes;
use paralegal_spdg::NodeCluster;
use paralegal_spdg::{Identifier, InstructionInfo, Node as SPDGNode, SPDG};
use std::sync::Arc;
use std::sync::OnceLock;

static TEST_CTX: OnceLock<Arc<Context>> = OnceLock::new();

pub fn test_ctx() -> Arc<Context> {
    TEST_CTX
        .get_or_init(|| {
            paralegal_flow::test_utils::run_paralegal_flow_with_flow_graph_dump("tests/test-crate");
            let desc = PreFrg::from_file_at("tests/test-crate").desc;
            Arc::new(Context::new(desc))
        })
        .clone()
}

pub fn get_callsite_or_datasink_node<'a>(
    ctx: &'a Context,
    controller: ControllerId,
    name: &'a str,
) -> NodeCluster {
    get_callsite_node(ctx, controller, name)
        .extended(&get_sink_node(ctx, controller, name))
        .unwrap()
}

pub fn get_callsite_node<'a>(
    ctx: &'a Context,
    controller: ControllerId,
    name: &'a str,
) -> NodeCluster {
    let name = Identifier::new_intern(name);
    let ctrl = &ctx.desc().controllers[&controller];
    let inner = ctrl
        .all_sources()
        .filter(|node| is_at_function_call_with_name(ctx, ctrl, name, *node));
    NodeCluster::new(controller, inner)
}

fn is_at_function_call_with_name(
    ctx: &Context,
    ctrl: &SPDG,
    name: Identifier,
    node: SPDGNode,
) -> bool {
    let weight = ctrl.graph.node_weight(node).unwrap().at;
    let instruction = &ctx.desc().instruction_info[&weight.leaf()];
    matches!(
        instruction,
        InstructionInfo::FunctionCall(call) if
            ctx.desc().def_info[&call.id].name == name
    )
}

pub fn get_sink_node<'a>(ctx: &'a Context, controller: ControllerId, name: &'a str) -> NodeCluster {
    let name = Identifier::new_intern(name);
    let ctrl = &ctx.desc().controllers[&controller];
    let inner = ctrl
        .data_sinks()
        .filter(|sink| is_at_function_call_with_name(ctx, ctrl, name, *sink));
    NodeCluster::new(controller, inner)
}
