use crate::Context;
use crate::ControllerId;
use crate::Node;
use paralegal_flow::test_utils::PreFrg;
use paralegal_spdg::DataSink;
use paralegal_spdg::Identifier;
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
) -> Option<Node<'a>> {
    Some(get_callsite_node(ctx, controller, name).unwrap_or(get_sink_node(ctx, controller, name)?))
}

pub fn get_callsite_node<'a>(
    ctx: &'a Context,
    controller: ControllerId,
    name: &'a str,
) -> Option<Node<'a>> {
    let name = Identifier::new_intern(name);
    let node = ctx.desc().controllers[&controller]
        .call_sites()
        .find(|callsite| ctx.desc().def_info[&callsite.function].name == name)?;
    Some(crate::Node {
        ctrl_id: controller,
        typ: node.into(),
    })
}

pub fn get_sink_node<'a>(
    ctx: &'a Context,
    controller: ControllerId,
    name: &'a str,
) -> Option<Node<'a>> {
    let name = Identifier::new_intern(name);
    let node = ctx.desc().controllers[&controller]
        .data_sinks()
        .find(|sink| match sink {
            DataSink::Argument { function, .. } => {
                ctx.desc().def_info[&function.function].name == name
            }
            _ => false,
        })?;
    Some(crate::Node {
        ctrl_id: controller,
        typ: node.into(),
    })
}
