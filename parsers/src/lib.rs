use definitions::parse_definitions;
use nom::{IResult, error::{VerboseError, context}, combinator::{all_consuming, opt}, sequence::tuple};
use policy_body::parse_policy_body;

pub type Res<T, U> = IResult<T, U, VerboseError<T>>;

// Top-level policy / definition data
#[derive(Debug, PartialEq, Eq)]
pub struct Policy<'a> {
    definitions: Vec<Definition<'a>>,
    body: PolicyBody<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum PolicyScope<'a> {
    Always,
    Sometimes,
    InCtrler(&'a str)
}

#[derive(Debug, PartialEq, Eq)]
pub struct PolicyBody<'a> {
    scope: PolicyScope<'a>,
    body: ASTNode<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Definition<'a> {
    // quantifier is always "all" bc definitions are over *each* var that satisifes condition
    variable: Variable<'a>,
    declaration: VariableIntro<'a>,
    filter: ASTNode<'a>
}

// AST data
#[derive(Debug, PartialEq, Eq)]
pub enum VariableIntro<'a> {
    Roots,
    Variable(Variable<'a>),
    VariableMarked((Variable<'a>, Marker<'a>)),
    VariableOfTypeMarked((Variable<'a>, Marker<'a>)),
    VariableSourceOf((Variable<'a>, Variable<'a>))
}

#[derive(Debug, PartialEq, Eq)]
pub enum Relation<'a> {
    Influences((Variable<'a>, Variable<'a>)),
    DoesNotInfluence((Variable<'a>, Variable<'a>)),
    FlowsTo((Variable<'a>, Variable<'a>)),
    NoFlowsTo((Variable<'a>, Variable<'a>)),
    ControlFlow((Variable<'a>, Variable<'a>)),
    NoControlFlow((Variable<'a>, Variable<'a>)),
    AssociatedCallSite((Variable<'a>, Variable<'a>)),
    IsMarked((Variable<'a>, Marker<'a>)),
    IsNotMarked((Variable<'a>, Marker<'a>)),
    OnlyVia((VariableIntro<'a>, VariableIntro<'a>, VariableIntro<'a>))
}

pub type Variable<'a> = &'a str;
pub type Marker<'a> = &'a str;

#[derive(Debug, PartialEq, Eq)]
pub enum Operator {
    And,
    Or,
}

// map templates to their handlebars template file names
impl<'a> From<VariableIntro<'a>> for &str {
    fn from(value: VariableIntro<'a>) -> Self {
        match value {
            VariableIntro::Roots => "roots",
            VariableIntro::Variable(_) => "variable",
            VariableIntro::VariableMarked(_) => "variable-marked",
            VariableIntro::VariableOfTypeMarked(_) => "variable-of-type-marked",
            VariableIntro::VariableSourceOf(_) =>  "variable-source-of",
        }
    }
}

impl<'a> From<Relation<'a>> for &str {
    fn from(value: Relation<'a>) -> Self {
        match value {
            Relation::FlowsTo(_) => "flows-to",
            Relation::NoFlowsTo(_) => "no-flows-to",
            Relation::ControlFlow(_) => "control-flow",
            Relation::NoControlFlow(_) => "no-control-flow",
            Relation::OnlyVia(_) => "only-via",
            Relation::AssociatedCallSite(_) => "associated-call-site",
            Relation::IsMarked(_) => "is-marked",
            Relation::IsNotMarked(_) => "is-not-marked",
            Relation::Influences(_) => "influences",
            Relation::DoesNotInfluence(_) => "does-not-influence",
        }
    }
}

impl From<Operator> for &str {
    fn from(value: Operator) -> Self {
        match value {
            Operator::And => "and",
            Operator::Or => "or",
        }
    }
}

impl From<&str> for Operator {
    fn from(value: &str) -> Self {
        match value {
            "and" => Operator::And,
            "or" => Operator::Or,
            _ => unimplemented!("invalid operator: valid options are 1) and 2) or")
        }
    }
}

impl<'a> From<PolicyScope<'a>> for &str {
    fn from(value: PolicyScope<'a>) -> Self {
        match value {
            PolicyScope::Always => "always",
            PolicyScope::Sometimes => "sometimes",
            PolicyScope::InCtrler(_) => "in-ctrler",
        }
    }
}

impl<'a> From<ClauseIntro<'a>> for &str {
    fn from(value: ClauseIntro<'a>) -> Self {
        match value {
            ClauseIntro::ForEach(_) => "for-each",
            ClauseIntro::ThereIs(_) => "there-is",
            ClauseIntro::Conditional(_) => "conditional",
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TwoNodeObligation<'a> {
    pub op: Operator,
    pub src: ASTNode<'a>,
    pub dest: ASTNode<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ClauseIntro<'a> {
    ForEach(VariableIntro<'a>),
    ThereIs(VariableIntro<'a>),
    Conditional(Relation<'a>)
}

#[derive(Debug, PartialEq, Eq)]
pub struct Clause<'a> {
    pub intro: ClauseIntro<'a>,
    pub body: ASTNode<'a>
}

#[derive(Debug, PartialEq, Eq)]
pub enum ASTNode<'a> {
    Relation(Relation<'a>),
    Clause(Box<Clause<'a>>),
    JoinedNodes(Box<TwoNodeObligation<'a>>)
}

pub fn parse<'a>(s: &'a str) -> Res<&str, Policy<'a>> {
    let mut combinator = context(
        "parse policy", 
        all_consuming(
            tuple((opt(parse_definitions), parse_policy_body))
        )
    );

    let (remainder, (option_defs, body)) = combinator(s)?;
    Ok((remainder, Policy {definitions: option_defs.unwrap_or_default(), body}))
}

pub mod common;
pub mod clause;
pub mod definitions;
pub mod policy_body;
pub mod relations;
pub mod scope;
pub mod variable_intro;