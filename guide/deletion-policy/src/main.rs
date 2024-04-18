use anyhow::Result;
use paralegal_policy::{
    assert_error,
    paralegal_spdg::rustc_portable::{DefId, LocalDefId},
    paralegal_spdg::traverse::EdgeSelection,
    paralegal_spdg::GlobalNode,
    paralegal_spdg::SPDG,
    Context, ControllerId, Marker,
    diagnostics::highlighted_node_span
};
use std::sync::Arc;
use colored::color::*;

extern crate strum_macros;

fn main() -> Result<()> {
    let dir = "../file-db-example/";
    paralegal_policy::SPDGGenCommand::global()
        .external_annotations("external-annotations.toml")
        .abort_after_analysis()
        .run(dir)?
        .with_context(paper_deletion_policy)?;
    println!("Policy successful");
    Ok(())
}

// #[derive(strum_macros::AsRefStr)]
enum Eval {
    Not(Box<Eval>),
    Src { code: &'static str, result: bool },
    All(Vec<IterItem>),
    Any(Vec<IterItem>),
    Or { left: Box<Eval>, right: Box<Eval> },
    And { left: Box<Eval>, right: Box<Eval> },
}

struct IterItem {
    item_rendering: String,
    body_eval: Eval,
}

impl Eval {
    fn success(&self) -> bool {
        match self {
            Self::Src { result, .. } => *result,
            Self::All(children) => children.iter().all(|c| c.body_eval.success()),
            Self::Any(children) => children.iter().any(|c| c.body_eval.success()),
            Self::Not(inner) => !inner.success(),
            Self::Or { left, right } => left.success() || right.success(),
            Self::And { left, right } => left.success() && right.success(),
        }
    }

    fn children_where(&self, expectation: bool) -> Vec<(String, &Eval)> {
        let mut succeeding = vec![];
        match self {
            Self::All(children) => succeeding.extend(
                children
                    .iter() // : Iterator<Item = &IterItem>
                    .filter(|c| c.body_eval.success() != expectation)
                    .map(|c| (format!("i = {}", &c.item_rendering), &c.body_eval)),
            ),
            Self::Not(inner) if inner.success() == expectation => {
                succeeding.push(("not".to_owned(), inner.as_ref()))
            }
            Self::Or { left, right } => succeeding.extend(
                [
                    ("left hand side".to_owned(), left.as_ref()),
                    ("right hand side".to_owned(), right.as_ref()),
                ]
                .into_iter()
                .filter(|c| expectation != c.1.success()),
            ),
            Self::And { left, right } => succeeding.extend(
                [
                    ("left hand side".to_owned(), left.as_ref()),
                    ("right hand side".to_owned(), right.as_ref()),
                ]
                .into_iter()
                .filter(|c| expectation != c.1.success()),
            ),
            Self::Any(children) => succeeding.extend(
                children
                    .iter()
                    .filter(|c| c.body_eval.success() != expectation)
                    .map(|c| (format!("i = {}", &c.item_rendering), &c.body_eval)),
            ),
            _ => (),
        }
        succeeding
    }

    fn all<D: Show>(iterator: Vec<D>, mut body: impl FnMut(D) -> Eval) -> Eval {
        Self::All(
            iterator
                .into_iter()
                .map(|item| IterItem {
                    item_rendering: format!("{}", DisplayAsShow(&item)),
                    body_eval: body(item),
                })
                .collect(),
        )
    }
    fn any<D: Show>(iterator: Vec<D>, mut body: impl FnMut(D) -> Eval) -> Eval {
        Self::Any(
            iterator
                .into_iter()
                .map(|item| IterItem {
                    item_rendering: format!("{}", DisplayAsShow(&item)),
                    body_eval: body(item),
                })
                .collect(),
        )
    }

    fn or(left: Eval, right: Eval) -> Eval {
        Self::Or {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
    fn and(left: Eval, right: Eval) -> Eval {
        Self::And {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
    fn not(expr: Eval) -> Eval {
        Self::Not(Box::new(expr))
    }

    fn emit(&self, prefix: &str, expectation: bool) {
        if self.success() != expectation {
            println!("{prefix}'{}' operator failed", self.as_ref());
            if let Self::All(inner) = self {
                if inner.is_empty() {
                    println!("{prefix}empty children");
                }
            } else if let Self::Any(inner) = self {
                if inner.is_empty() {
                    println!("{prefix}empty children");
                }
            }
            for (message, inner) in self.children_where(expectation).into_iter().take(1) {
                println!("{prefix}Inner failure from {message}");
                inner.emit(
                    &format!("  {prefix}"),
                    match self {
                        Self::Not { .. } => !expectation,
                        _ => expectation,
                    },
                )
            }
        }
    }
    fn as_ref(&self) -> &str {
        match self {
            Self::Not { .. } => "not",
            Self::Or { .. } => "or",
            Self::All { .. } => "all",
            Self::Src { code, .. } => code,
            Self::Any {..} => "any",
            Self::And { .. } => "and",
            _ => "other",
        }
    }
}

// trait FlowsTo {
//     fn flows<T>(&self, _: &T) -> bool
//     where
//         T: ?Sized,
//     {
//         false
//     }
// }

// impl<T> FlowsTo for T {}

macro_rules! src {
    ($($code:tt)*) => {
        Eval::Src {
            result: $($code)*,
            code: stringify!($($code)*),
        }
    }
}

// fn dummy_policy(_: Arc<Context>) -> Result<()> {
//     let my_policy_result = Eval::all(vec!["hello", "there"], |s: &str| {
//         Eval::all(vec![1, 2, 3], |i: u32| {
//             Eval::or(src!(s.flows(&i)), src!(i.flows(s)))
//         })
//     });
//     my_policy_result.emit("", true);
//     Ok(())
// }

// #[allow(dead_code)]
// fn deletion_policy(ctx: Arc<Context>) -> Result<()> {
//     let my_policy_result = Eval::any(ctx.all_controllers().collect(), |(deleter_id, _ignored)| {
//         Eval::all(ctx.marked_type(Marker::new_intern("user_data")).iter().collect(), |&t| {
//             Eval::any(ctx.srcs_with_type(deleter_id, t).collect(), |src| {
//                 Eval::any(
//                     ctx
//                     .all_nodes_for_ctrl(deleter_id)
//                     .filter(|n| ctx.has_marker(Marker::new_intern("deletes"), *n))
//                     .collect::<Vec<_>>(), |sink| {
//                         src!(ctx.flows_to(src, sink, EdgeSelection::Data))
//                     })
//             })
//         })
//     });
//     my_policy_result.emit("", true);
//     Ok(())
// }

#[allow(dead_code)]
fn deletion_policy(ctx: Arc<Context>) -> Result<()> {
    let my_policy_result = Eval::any(ctx.all_controllers().collect(), |(deleter_id, _ignored)| {
        Eval::all(
            ctx.marked_type(Marker::new_intern("user_data"))
                .iter()
                .collect(),
            |&t| {
                Eval::any(ctx.srcs_with_type(deleter_id, t).collect(), |src| {
                    Eval::any(
                        ctx.all_nodes_for_ctrl(deleter_id)
                            .filter(|n| ctx.has_marker(Marker::new_intern("deletes"), *n))
                            .collect::<Vec<_>>(),
                        |sink| src!(ctx.flows_to(src, sink, EdgeSelection::Data)),
                    )
                })
            },
        )
    });
    my_policy_result.emit("", true);
    Ok(())
}

fn paper_deletion_policy(ctx: Arc<Context>) -> Result<()> {
    let my_policy_result = Eval::any(ctx.all_controllers().collect(), |(deleter_id, _ignored)| {
        Eval::all(
            ctx.marked_type(Marker::new_intern("user_data"))
                .iter()
                .collect(),
            |&t| {
                Eval::any(ctx.srcs_with_type(deleter_id, t).collect(), |src| {
                    Eval::any(
                        ctx.all_nodes_for_ctrl(deleter_id)
                            .filter(|n| ctx.has_marker(Marker::new_intern("make_delete_query"), *n))
                            .collect::<Vec<_>>(),
                        |sink| Eval::and(
                            src!(ctx.flows_to(src, sink, EdgeSelection::Data)),
                            Eval::any(
                                ctx.all_nodes_for_ctrl(deleter_id)
                                    .filter(|n| ctx.has_marker(Marker::new_intern("executes"), *n))
                                    .collect::<Vec<_>>(),
                                |exec| {
                                    src!(ctx.flows_to(sink, exec, EdgeSelection::Data))
                                })
                        )
                    )
                })
            },
        )
    });
    my_policy_result.emit("", true);
    Ok(())
}

use paralegal_policy::diagnostics::HighlightedSpan;

struct DisplayAsShow<'a, T>(&'a T);

impl<T: Show> std::fmt::Display for DisplayAsShow<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>, ctx : &Context) -> std::fmt::Result {
        self.0.show(f, ctx) // JUSTUS
    }
}

trait Show {
    fn show(&self, f: &mut std::fmt::Formatter<'_>, ctx: &Context) -> std::fmt::Result;
}

impl Show for &DefId {
    fn show(&self, f: &mut std::fmt::Formatter<'_>, ctx: &Context) -> std::fmt::Result {
        write!(f, "{}", ctx.desc().def_info[self].name)
    }
}
impl Show for LocalDefId {
    fn show(&self, f: &mut std::fmt::Formatter<'_>, ctx: &Context) -> std::fmt::Result {
        write!(f, "{}", ctx.desc().def_info[&self.to_def_id()].name)
    }
}
impl Show for &SPDG {
    fn show(&self, f: &mut std::fmt::Formatter<'_>, ctx: &Context) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}
impl Show for (LocalDefId, &SPDG) {
    fn show(&self, f: &mut std::fmt::Formatter<'_>, ctx: &Context) -> std::fmt::Result {
        self.0.show(f, ctx)?;
        self.1.show(f, ctx)
    }
}
// impl Show for ControllerId {
//     fn show(&self, f: &mut std::fmt::Formatter<'_>, ctx: &Context) -> std::fmt::Result {
//         write!(f, "{}", ctx.desc().def_info[self].name)
//     }
// }

impl Show for GlobalNode {
    fn show(&self, f: &mut std::fmt::Formatter<'_>, ctx: &Context) -> std::fmt::Result {
        let span : HighlightedSpan = highlighted_node_span(ctx, *self);
        writeln!(f, "");
        span.write(f, Color::Black)
    }
}