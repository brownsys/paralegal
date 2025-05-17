use std::{
    cmp::{max_by, max_by_key},
    fmt::Display,
    sync::Arc,
};

use paralegal_spdg::{
    traverse::EdgeSelection, DisplayPath, Endpoint, GlobalNode, Identifier, IntoIterGlobalNodes,
    NodeCluster,
};

use crate::{
    diagnostics::{ControllerContext, Diagnostic, DiagnosticBuilder, HasDiagnosticsBase},
    Context, Diagnostics, NodeQueries,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Relation {
    GoesTo,
    GoesToAll,
    Influences,
    InfluencesAll,
    HasCtrlInfluence,
    HasCtrlInfluenceAll,
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

struct DisplayRule<'a>(&'a str);

impl Display for DisplayRule<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            Ok(())
        } else {
            write!(f, "(Rule {})", self.0)
        }
    }
}

struct DisplaySpan<'a>(&'a str);

impl Display for DisplaySpan<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            Ok(())
        } else {
            write!(f, "`{}`", self.0)
        }
    }
}

impl Cause {
    fn report<'a, B: HasDiagnosticsBase>(
        &self,
        result: bool,
        msg: &mut DiagnosticBuilder<'a, B>,
        ctx: &impl Context,
    ) {
        match &self.ty {
            CauseTy::Vacuous => {
                msg.with_note(format!(
                    "{} {}\nis vacuously {}",
                    DisplaySpan(self.description.as_str()),
                    DisplayRule(self.clause_ident.as_str()),
                    if result { "true" } else { "false" }
                ));
            }
            CauseTy::Binop {
                left,
                right,
                relation,
            } => {
                msg.with_node_note(
                    *left,
                    format!(
                        "{} {}\nwith source",
                        DisplaySpan(self.description.as_str()),
                        DisplayRule(self.clause_ident.as_str())
                    ),
                )
                .with_node_note(
                    *right,
                    format!(
                        "does {}{}",
                        if result { "" } else { "not " },
                        match relation {
                            Relation::GoesTo | Relation::GoesToAll => "go to",
                            Relation::Influences | Relation::InfluencesAll => "influence",
                            Relation::HasCtrlInfluence | Relation::HasCtrlInfluenceAll =>
                                "have control influence on",
                        }
                    ),
                );
            }
            CauseTy::OnlyVia { from, to } => {
                msg.with_node_note(
                    *from,
                    format!(
                        "{} {}\nsource",
                        DisplaySpan(self.description.as_str()),
                        DisplayRule(self.clause_ident.as_str())
                    ),
                );
                if let Some(to) = to {
                    msg.with_node_note(
                        *to,
                        format!(
                            "{} data flow influence on this target without passing checkpoint",
                            if result { "does not have" } else { "has" },
                        ),
                    );
                } else {
                    msg.with_note(format!(
                        "{} data flow influence without passing checkpoint",
                        if result { "does not have" } else { "has" },
                    ));
                }
            }
            CauseTy::Not(inner) => {
                inner.report(!result, msg, ctx);
            }
            CauseTy::Connective {
                connective: _,
                fail,
            } => {
                msg.with_note(format!(
                    "{} {} {}",
                    DisplaySpan(self.description.as_str()),
                    if result { "succeeded" } else { "failed" },
                    DisplayRule(self.clause_ident.as_str())
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
                            "{} {}\n{} because of item",
                            DisplaySpan(self.description.as_str()),
                            DisplayRule(self.clause_ident.as_str()),
                            classification
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
                        "{} {}\n{classification} because of {item_name}",
                        DisplaySpan(self.description.as_str()),
                        DisplayRule(self.clause_ident.as_str()),
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
    OnlyVia {
        from: GlobalNode,
        to: Option<GlobalNode>,
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
    Vacuous,
}

impl CauseTy {
    pub fn empty_quantifier(connective: Connective) -> Self {
        Self::Quantifier {
            connective,
            item: QuantifierItem::Empty,
            inner_cause: None,
        }
    }
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

impl<T> From<Arc<T>> for QuantifierItem
where
    QuantifierItem: for<'a> From<&'a T>,
{
    fn from(value: Arc<T>) -> Self {
        QuantifierItem::from(value.as_ref())
    }
}

impl From<&ControllerContext> for QuantifierItem {
    fn from(value: &ControllerContext) -> Self {
        QuantifierItem::Endpoint(value.id())
    }
}

impl CauseTy {
    fn progress(&self) -> u32 {
        match self {
            Self::Binop { .. } | Self::OnlyVia { .. } => 1,
            Self::Not(inner) => inner.ty.progress() + 1,
            Self::Quantifier { inner_cause, .. } => {
                inner_cause.as_ref().map_or(0, |inner| inner.ty.progress()) + 1
            }
            Self::Connective { fail, .. } => fail.ty.progress() + 1,
            Self::Vacuous => 1,
        }
    }
}

type EvalResult = (bool, Cause);

#[derive(Clone, Copy)]
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

    pub fn with_type(self, ty: CauseTy) -> Cause {
        Cause {
            description: self.description.into(),
            clause_ident: self.clause_num.into(),
            ty,
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

    pub fn goes_to(
        self,
        left: impl IntoIterGlobalNodes,
        right: impl IntoIterGlobalNodes,
        ctx: &impl Context,
    ) -> EvalResult {
        self.binop(Relation::GoesTo, left, right, ctx)
    }

    pub fn goes_to_all(
        self,
        left: impl IntoIterGlobalNodes,
        right: impl IntoIterGlobalNodes,
        ctx: &impl Context,
    ) -> EvalResult {
        self.binop(Relation::GoesToAll, left, right, ctx)
    }

    pub fn influences(
        self,
        left: impl IntoIterGlobalNodes,
        right: impl IntoIterGlobalNodes,
        ctx: &impl Context,
    ) -> EvalResult {
        self.binop(Relation::Influences, left, right, ctx)
    }

    pub fn influences_all(
        self,
        left: impl IntoIterGlobalNodes,
        right: impl IntoIterGlobalNodes,
        ctx: &impl Context,
    ) -> EvalResult {
        self.binop(Relation::InfluencesAll, left, right, ctx)
    }

    pub fn has_ctrl_influence(
        self,
        left: impl IntoIterGlobalNodes,
        right: impl IntoIterGlobalNodes,
        ctx: &impl Context,
    ) -> EvalResult {
        self.binop(Relation::HasCtrlInfluence, left, right, ctx)
    }

    pub fn has_ctrl_influence_all(
        self,
        left: impl IntoIterGlobalNodes,
        right: impl IntoIterGlobalNodes,
        ctx: &impl Context,
    ) -> EvalResult {
        self.binop(Relation::HasCtrlInfluenceAll, left, right, ctx)
    }

    fn binop(
        self,
        relation: Relation,
        left: impl IntoIterGlobalNodes,
        right: impl IntoIterGlobalNodes,
        ctx: &impl Context,
    ) -> EvalResult {
        let sample_left = left.iter_global_nodes().next().unwrap();
        let sample_right = right.iter_global_nodes().next().unwrap();

        let mk_clause = |left, right| Cause {
            description: self.description,
            clause_ident: self.clause_num,
            ty: CauseTy::Binop {
                left,
                right,
                relation,
            },
        };

        let clause_from_option = |opt: Option<(GlobalNode, GlobalNode)>| {
            (
                opt.is_some(),
                opt.map_or_else(
                    || mk_clause(sample_left, sample_right),
                    |(src, sink)| mk_clause(src, sink),
                ),
            )
        };

        let clause_from_cluster = |cluster: Option<NodeCluster>| {
            (
                !cluster.is_some(),
                cluster.map_or_else(
                    || mk_clause(sample_left, sample_right),
                    |cluster| mk_clause(sample_left, cluster.iter_global_nodes().next().unwrap()),
                ),
            )
        };

        match relation {
            Relation::GoesTo => {
                clause_from_option(left.find_flow(right, ctx.root(), EdgeSelection::Data))
            }
            Relation::HasCtrlInfluence => {
                clause_from_option(left.find_ctrl_influence(right, ctx.root()))
            }
            Relation::Influences => {
                clause_from_option(left.find_flow(right, ctx.root(), EdgeSelection::Both))
            }
            Relation::InfluencesAll => {
                clause_from_cluster(left.flows_to_all(right, ctx.root(), EdgeSelection::Both))
            }
            Relation::GoesToAll => {
                clause_from_cluster(left.flows_to_all(right, ctx.root(), EdgeSelection::Data))
            }
            Relation::HasCtrlInfluenceAll => {
                clause_from_cluster(left.has_ctrl_influence_all(right, ctx.root()))
            }
        }
    }

    pub fn only_via(
        self,
        starting: impl IntoIterator<Item = GlobalNode>,
        is_checkpoint: impl FnMut(GlobalNode) -> bool,
        is_terminal: impl FnMut(GlobalNode) -> bool,
        ctx: &impl Context,
    ) -> EvalResult {
        let mut starting = starting.into_iter().peekable();
        let Some(a_start) = starting.peek().copied() else {
            return (
                true,
                Cause {
                    description: self.description,
                    clause_ident: self.clause_num,
                    ty: CauseTy::Vacuous,
                },
            );
        };
        let result = ctx
            .root()
            .always_happens_before(starting, is_checkpoint, is_terminal)
            .unwrap();
        let (from, to) = if result.holds() {
            let res = result.reached().expect(
                "With error message the only-via trace level needs to be at least start-and-end",
            );
            let (a, b) = res.first().expect("Trace should not be empty");
            (*a, Some(*b))
        } else {
            (a_start, None)
        };
        (
            result.holds(),
            Cause {
                description: self.description,
                clause_ident: self.clause_num,
                ty: CauseTy::OnlyVia { from, to },
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
