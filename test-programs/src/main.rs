use anyhow::Result;
use paralegal_policy::{
    assert_error, paralegal_spdg::Identifier, Context, Diagnostics, EdgeType, Marker, Node,
};
use std::sync::Arc;

pub mod flows_to;

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
    let mut sensitive_nodes = ctx.marked_nodes(marker!(private_key));
    let mut encrypts_nodes = ctx.marked_nodes(marker!(encrypt_func));
    assert_error!(ctx, sensitive_nodes.any(|sensitive| encrypts_nodes.any(|encrypts| ctx.flows_to(sensitive, encrypts, EdgeType::Data))));
    Ok(())
});

fn main() -> Result<()> {
    let dir = ".";
    let cmd = paralegal_policy::SPDGGenCommand::global();
    cmd.run(dir)?.with_context(pol)?;
    println!("Policy successful");
    Ok(())
}
