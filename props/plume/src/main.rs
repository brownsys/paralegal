use anyhow::{anyhow, Result};
use std::sync::Arc;

use paralegal_policy::{
    assert_error,
    paralegal_spdg::{rustc_portable::DefId, Ctrl, DefKind},
    Context, ControllerId, Marker,
};

macro_rules! marker {
    ($id:ident) => {
        Marker::new_intern(stringify!($id))
    };
}

struct DisplayDef<'a> {
    def_id: DefId,
    ctx: &'a Context,
}

impl<'a> std::fmt::Display for DisplayDef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Write;
        let info = &self.ctx.desc().def_info[&self.def_id];
        f.write_str(match info.kind {
            DefKind::Type => "type",
            DefKind::Function => "function",
        })?;
        f.write_str(" `")?;
        for segment in &info.path {
            f.write_str(segment.as_str())?;
            f.write_str("::")?;
        }
        f.write_str(info.name.as_str())?;
        f.write_char('`')
    }
}

trait ContextExt {
    fn controllers<'a>(&'a self) -> Box<dyn Iterator<Item = (ControllerId, &'a Ctrl)> + 'a>;
    fn marked_type<'a>(&'a self, marker: Marker) -> Box<dyn Iterator<Item = DefId> + 'a>;
    fn describe_def<'a>(&'a self, def_id: DefId) -> DisplayDef<'a>;
}

impl ContextExt for Context {
    fn controllers<'a>(&'a self) -> Box<dyn Iterator<Item = (ControllerId, &'a Ctrl)> + 'a> {
        Box::new(self.desc().controllers.iter().map(|(k, v)| (*k, v))) as Box<_>
    }

    fn marked_type<'a>(&'a self, marker: Marker) -> Box<dyn Iterator<Item = DefId> + 'a> {
        Box::new(
            self.marked(marker)
                .filter(|(did, _)| self.desc().def_info[did].kind == DefKind::Type)
                .map(|(did, refinement)| {
                    assert!(refinement.on_self());
                    *did
                }),
        ) as Box<_>
    }
    fn describe_def<'a>(&'a self, def_id: DefId) -> DisplayDef<'a> {
        DisplayDef { ctx: self, def_id }
    }
}

// all c : Ctrl | all u : labeled_objects_with_types[c, Object, user, labels] | some deleter: labeled_objects[CallArgument, to_delete, labels] |
// (flows_to_unmodified[c, u, deleter, flow_set])
// implies {
//     all user_type : labeled_objects[Type, user_data, labels] | { // for all Types representing user data
// 		some arg : labeled_objects[CallArgument, to_delete, labels] | {
// 			flows_to[c, user_type, arg, flow_set] // that data is deleted
// 		}
// 	}
// }
fn check(ctx: Arc<Context>) -> Result<()> {
    let found = ctx
        .controllers()
        .collect::<Vec<_>>()
        .into_iter()
        .any(|(deleter_id, deleter)| {
            ctx.marked_type(marker!(user_data))
                .collect::<Vec<_>>()
                .into_iter()
                .all(|t| {
                    let sources = ctx.srcs_with_type(deleter, t).collect::<Vec<_>>();
                    deleter
                        .data_flow
                        .values()
                        .flat_map(|snks| snks.iter())
                        .any(|sink| {
                            sources
                                .iter()
                                .any(|src| ctx.flows_to(deleter_id, src, sink))
                        })
                })
        });
    assert_error!(ctx, found, "Could not find a function deleting all types");
    Ok(())
}

fn main() -> Result<()> {
    let dir = std::env::args()
        .nth(1)
        .ok_or_else(|| anyhow!("expected plume directory as argument"))?;
    let mut cmd = paralegal_policy::SPDGGenCommand::global();
    cmd.get_command().args([
        "--external-annotations",
        "external-annotations.toml",
        "--abort-after-analysis",
        "--inline-elision",
        "--target",
        "plume_models",
        "--",
        "--no-default-features",
        "--features",
        "postgres",
    ]);
    cmd.run(dir)?.with_context(check)
}
