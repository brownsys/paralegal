use anyhow::Result;
use paralegal_policy::{
    assert_error, paralegal_spdg::Identifier, Context, Diagnostics, EdgeType, Marker, Node,
};
use std::sync::Arc;

macro_rules! marker {
    ($name:ident) => {{
        lazy_static::lazy_static! {
            static ref MARKER: Marker = Identifier::new_intern(stringify!($name));
        }
        *MARKER
    }};
}

macro_rules! policy {
    ($name:ident $(,)? $context:ident $(,)? $code:block) => {
        fn $name(ctx: Arc<Context>) -> Result<()> {
            ctx.named_policy(Identifier::new_intern(stringify!($name)), |$context| $code)
        }
    };
}

trait ContextExt {
    fn marked_nodes<'a>(&'a self, marker: Marker) -> Box<dyn Iterator<Item = Node<'a>> + 'a>;
}

impl ContextExt for Context {
    fn marked_nodes<'a>(&'a self, marker: Marker) -> Box<dyn Iterator<Item = Node<'a>> + 'a> {
        Box::new(
            self.desc()
                .controllers
                .keys()
                .copied()
                .flat_map(move |k| self.all_nodes_for_ctrl(k))
                .filter(move |node| self.has_marker(marker, *node)),
        )
    }
}

policy!(pol, ctx {
    for c_id in ctx.desc().controllers.keys() {
        let mut comm_bc_nodes = ctx.all_nodes_for_ctrl(*c_id).filter(|n| self.cx.has_marker(marker!(community_ban_check), *n));
        let mut comm_data_nodes = ctx.all_nodes_for_ctrl(*c_id).filter(|n| self.cx.has_marker(marker!(community_data), *n));
        let mut comm_dc_nodes = ctx.all_nodes_for_ctrl(*c_id).filter(|n| self.cx.has_marker(marker!(community_delete_check), *n));
        let mut write_nodes = ctx.all_nodes_for_ctrl(*c_id).filter(|n| self.cx.has_marker(marker!(db_write), *n));

        let is_compliant =
            comm_data_nodes.any(|comm_data| {
                write_nodes.all(|write| {
                    if ctx.flows_to(comm_data, write, EdgeType::Data) {
                            comm_dc_nodes.any(|comm_dc| {
                                ctx.flows_to(comm_data, comm_dc, EdgeType::Data)
                                &&
                                ctx.has_ctrl_influence(comm_dc, write)
                            })
                            &&
                            comm_bc_nodes.any(|comm_bc| {
                                ctx.flows_to(comm_data, comm_bc, EdgeType::Data)
                                &&
                                ctx.has_ctrl_influence(comm_bc, write)
                            })
                    }
                })
            });

        assert_error!(ctx, is_compliant, format!("Controller {} is not compliant with the policy", c_id));
    }
    Ok(())
});

fn main() -> Result<()> {
    let dir = ".";
    let cmd = paralegal_policy::SPDGGenCommand::global();
    cmd.run(dir)?.with_context(pol)?;
    println!("Policy successful");
    Ok(())
}
