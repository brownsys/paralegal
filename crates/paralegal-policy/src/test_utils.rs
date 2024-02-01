use crate::Context;
use crate::ControllerId;
use paralegal_flow::test_utils::PreFrg;
use paralegal_spdg::{GlobalNode, Identifier, InstructionInfo, Node as SPDGNode, SPDG};
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
) -> Option<GlobalNode> {
    Some(get_callsite_node(ctx, controller, name).unwrap_or(get_sink_node(ctx, controller, name)?))
}

pub fn get_callsite_node<'a>(
    ctx: &'a Context,
    controller: ControllerId,
    name: &'a str,
) -> Option<GlobalNode> {
    let name = Identifier::new_intern(name);
    let ctrl = &ctx.desc().controllers[&controller];
    let inner = ctrl
        .call_sites()
        .find(|callsite| is_at_function_call_with_name(ctx, ctrl, name, *callsite))?;
    Some(GlobalNode::from_local_node(controller, inner))
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

pub fn get_sink_node<'a>(
    ctx: &'a Context,
    controller: ControllerId,
    name: &'a str,
) -> Option<GlobalNode> {
    let name = Identifier::new_intern(name);
    let ctrl = &ctx.desc().controllers[&controller];
    let inner = ctrl
        .data_sinks()
        .find(|sink| is_at_function_call_with_name(ctx, ctrl, name, *sink))?;
    Some(GlobalNode::from_local_node(controller, inner))
}
