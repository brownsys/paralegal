use std::{
    cmp::{max_by, max_by_key},
    fmt::Display,
};

use paralegal_spdg::{traverse::EdgeSelection, DisplayPath, Endpoint, GlobalNode, Identifier};

use crate::{
    diagnostics::{Diagnostic, DiagnosticBuilder, HasDiagnosticsBase},
    Context, Diagnostics, NodeQueries,
};

pub enum Relation {
    GoesTo,
    Influences,
    HasCtrlInfluence,
}

#[derive(Clone, Copy)]
pub enum Connective {
    And,
    Or,
}

pub struct Cause {
    description: Identifier,
    clause_ident: Identifier,
    ty: CauseTy,
}

impl Cause {
    fn report<'a, B: HasDiagnosticsBase>(
        &self,
        result: bool,
        msg: &mut DiagnosticBuilder<'a, B>,
        ctx: &impl Context,
    ) {
        match &self.ty {
            CauseTy::Binop {
                left,
                right,
                relation,
            } => {
                msg.with_node_note(
                    *left,
                    format!(
                        "`{}` (Rule {})\nwith source",
                        self.description, self.clause_ident
                    ),
                )
                .with_node_note(
                    *right,
                    format!(
                        "does {}{}",
                        if result { "" } else { "not " },
                        match relation {
                            Relation::GoesTo => "go to",
                            Relation::Influences => "influence",
                            Relation::HasCtrlInfluence => "have control influence on",
                        }
                    ),
                );
            }
            CauseTy::Not(inner) => {
                inner.report(!result, msg, ctx);
            }
            CauseTy::Connective {
                connective: _,
                fail,
            } => {
                msg.with_note(format!(
                    "`{}` {} (Rule {})",
                    self.description,
                    if result { "succeeded" } else { "failed" },
                    self.clause_ident
                ));
                fail.report(result, msg, ctx);
            }
            CauseTy::Quantifier {
                connective: _,
                item,
                inner_cause,
            } => {
                let classification = if result { "succeeded" } else { "failed" };
                if let QuantifierItem::Node(n) = &item {
                    msg.with_node_note(
                        *n,
                        format!(
                            "`{}` (Rule {})\n{} because of item",
                            self.description, self.clause_ident, classification
                        ),
                    );
                } else {
                    let item_name = match &item {
                        QuantifierItem::Empty => "No Matching Element".to_owned(),
                        QuantifierItem::Other(o) => format!("{o}"),
                        QuantifierItem::Endpoint(e) => {
                            format!(
                                "{}",
                                DisplayPath::from(&ctx.root().desc().def_info[&e].path)
                            )
                        }
                        QuantifierItem::Node(_) => unreachable!(),
                    };
                    msg.with_note(format!(
                        "`{}` (Rule {})\n{classification} because of {item_name}",
                        self.description, self.clause_ident,
                    ));
                }
                if let Some(inner) = inner_cause {
                    inner.report(result, msg, ctx);
                }
            }
        }
    }
}

pub enum CauseTy {
    Binop {
        left: GlobalNode,
        right: GlobalNode,
        relation: Relation,
    },
    /// In case of `Connective::Or` the item is the one with "lowest-down"
    /// failure, e.g. that made "the most progress" in the policy.
    Quantifier {
        connective: Connective,
        item: QuantifierItem,
        inner_cause: Option<Box<Cause>>,
    },
    Connective {
        connective: Connective,
        fail: Box<Cause>,
    },
    /// The inner cause type now describes successes
    Not(Box<Cause>),
}

pub enum QuantifierItem {
    Node(GlobalNode),
    Endpoint(Endpoint),
    Empty,
    Other(Box<dyn Display>),
}

impl From<GlobalNode> for QuantifierItem {
    fn from(value: GlobalNode) -> Self {
        QuantifierItem::Node(value)
    }
}

impl From<&GlobalNode> for QuantifierItem {
    fn from(value: &GlobalNode) -> Self {
        QuantifierItem::Node(*value)
    }
}

impl From<Endpoint> for QuantifierItem {
    fn from(value: Endpoint) -> Self {
        QuantifierItem::Endpoint(value)
    }
}

impl From<&Endpoint> for QuantifierItem {
    fn from(value: &Endpoint) -> Self {
        QuantifierItem::Endpoint(*value)
    }
}

impl CauseTy {
    fn progress(&self) -> u32 {
        match self {
            Self::Binop { .. } => 1,
            Self::Not(inner) => inner.ty.progress() + 1,
            Self::Quantifier { inner_cause, .. } => {
                inner_cause.as_ref().map_or(0, |inner| inner.ty.progress()) + 1
            }
            Self::Connective { fail, .. } => fail.ty.progress() + 1,
        }
    }
}

type EvalResult = (bool, Cause);

pub struct CauseBuilder {
    description: Identifier,
    clause_num: Identifier,
}

impl CauseBuilder {
    pub fn new(description: impl Into<Identifier>, clause_num: impl Into<Identifier>) -> Self {
        Self {
            description: description.into(),
            clause_num: clause_num.into(),
        }
    }

    pub fn not(self, inner: EvalResult) -> EvalResult {
        let (success, cause) = inner;
        (
            !success,
            Cause {
                description: self.description,
                clause_ident: self.clause_num,
                ty: CauseTy::Not(Box::new(cause)),
            },
        )
    }

    pub fn and(
        self,
        left: impl FnOnce() -> EvalResult,
        right: impl FnOnce() -> EvalResult,
    ) -> EvalResult {
        self.connective(left, right, Connective::And)
    }

    pub fn or(
        self,
        left: impl FnOnce() -> EvalResult,
        right: impl FnOnce() -> EvalResult,
    ) -> EvalResult {
        self.connective(left, right, Connective::Or)
    }

    fn connective(
        self,
        left: impl FnOnce() -> EvalResult,
        right: impl FnOnce() -> EvalResult,
        connective: Connective,
    ) -> EvalResult {
        let (l_success, l_cause) = left();
        let short_circuit = match connective {
            Connective::Or => true,
            Connective::And => false,
        };
        let (success, cause) = if l_success == short_circuit {
            (short_circuit, l_cause)
        } else {
            right()
        };
        (
            success,
            Cause {
                description: self.description,
                clause_ident: self.clause_num,
                ty: CauseTy::Connective {
                    connective,
                    fail: Box::new(cause),
                },
            },
        )
    }

    pub fn goes_to(self, left: GlobalNode, right: GlobalNode, ctx: &impl Context) -> EvalResult {
        self.binop(Relation::GoesTo, left, right, ctx)
    }

    pub fn influences(self, left: GlobalNode, right: GlobalNode, ctx: &impl Context) -> EvalResult {
        self.binop(Relation::Influences, left, right, ctx)
    }

    pub fn has_ctr_influence(
        self,
        left: GlobalNode,
        right: GlobalNode,
        ctx: &impl Context,
    ) -> EvalResult {
        self.binop(Relation::HasCtrlInfluence, left, right, ctx)
    }

    fn binop(
        self,
        relation: Relation,
        left: GlobalNode,
        right: GlobalNode,
        ctx: &impl Context,
    ) -> EvalResult {
        let result = match relation {
            Relation::GoesTo => left.flows_to(right, ctx.root(), EdgeSelection::Data),
            Relation::HasCtrlInfluence => left.has_ctrl_influence(right, ctx.root()),
            Relation::Influences => left.flows_to(right, ctx.root(), EdgeSelection::Both),
        };

        (
            result,
            Cause {
                description: self.description,
                clause_ident: self.clause_num,
                ty: CauseTy::Binop {
                    left,
                    right,
                    relation,
                },
            },
        )
    }

    pub fn all<I: Into<QuantifierItem>>(
        self,
        it: impl IntoIterator<Item = I>,
        f: impl FnMut(&I) -> EvalResult,
    ) -> EvalResult {
        self.quantifier(it, f, Connective::And)
    }

    pub fn any<I: Into<QuantifierItem>>(
        self,
        it: impl IntoIterator<Item = I>,
        f: impl FnMut(&I) -> EvalResult,
    ) -> EvalResult {
        self.quantifier(it, f, Connective::Or)
    }

    fn quantifier<I: Into<QuantifierItem>>(
        self,
        it: impl IntoIterator<Item = I>,
        mut f: impl FnMut(&I) -> EvalResult,
        connective: Connective,
    ) -> EvalResult {
        let mut cause = None;
        let mut progress = 0;
        let mk_result = |item, inner: Option<_>| Cause {
            description: self.description,
            clause_ident: self.clause_num,
            ty: CauseTy::Quantifier {
                connective,
                item,
                inner_cause: inner.map(Box::new),
            },
        };
        let short_circuit = match connective {
            Connective::Or => true,
            Connective::And => false,
        };
        for i in it {
            let (success, inner_cause) = f(&i);
            if success == short_circuit {
                return (short_circuit, mk_result(i.into(), Some(inner_cause)));
            }
            let inner_progress = inner_cause.ty.progress();
            if inner_progress > progress {
                cause = Some(inner_cause);
                progress = inner_progress;
            }
        }
        (!short_circuit, mk_result(QuantifierItem::Empty, cause))
    }
}

pub fn report((result, cause): EvalResult, ctx: &impl Context) -> bool {
    if !result {
        let mut msg = ctx.root().struct_error("Failed policy");
        cause.report(result, &mut msg, ctx);
        msg.emit();
    }
    result
}
