use anyhow::Result;
use paralegal_policy::{assert_error, paralegal_spdg::Identifier, Context, Diagnostics, EdgeType, Marker, Node};
use std::sync::Arc;

macro_rules! marker {
    ($name:ident) => ({
        lazy_static::lazy_static! {
            static ref MARKER: Marker = Identifier::new_intern(stringify!($name));
        }
        *MARKER
    });
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
        let mut bc_nodes = ctx.all_nodes_for_ctrl(*c_id).filter(|n| self.cx.has_marker(marker!(instance_ban_check), *n));
        let mut dc_nodes = ctx.all_nodes_for_ctrl(*c_id).filter(|n| self.cx.has_marker(marker!(instance_delete_check), *n));
        let mut read_nodes = ctx.all_nodes_for_ctrl(*c_id).filter(|n| self.cx.has_marker(marker!(db_read), *n));
        let mut write_nodes = ctx.all_nodes_for_ctrl(*c_id).filter(|n| self.cx.has_marker(marker!(db_write), *n));

        let is_compliant = 
            dc_nodes.any(|dc| {
                write_nodes.all(|write| {
                    ctx.has_ctrl_influence(dc, write)
                }) 
                &&
                read_nodes.all(|read| {
                    ctx.has_ctrl_influence(dc, read)
                })
            }) 
            &&
            bc_nodes.any(|bc| {
                write_nodes.all(|write| {
                    ctx.has_ctrl_influence(bc, write)
                }) 
                &&
                read_nodes.all(|read| {
                    ctx.has_ctrl_influence(bc, read)
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
