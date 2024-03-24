use definitions::parse_definitions;
use nom::{IResult, error::{VerboseError, context}, combinator::{all_consuming, opt}, sequence::tuple};
use policy_body::parse_policy_body;
use templates::Template;

pub type Res<T, U> = IResult<T, U, VerboseError<T>>;

// Top-level policy / definition data
#[derive(Debug, PartialEq, Eq)]
pub struct Policy<'a> {
    pub definitions: Vec<Definition<'a>>,
    pub scope: PolicyScope<'a>,
    pub body: ASTNode<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum PolicyScope<'a> {
    Always,
    Sometimes,
    InCtrler(&'a str)
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
impl<'a> From<VariableIntro<'a>> for Template {
    fn from(value: VariableIntro<'a>) -> Self {
        match value {
            VariableIntro::Roots => Template::Roots,
            VariableIntro::Variable(_) => Template::Variable,
            VariableIntro::VariableMarked(_) => Template::VariableMarked,
            VariableIntro::VariableOfTypeMarked(_) => Template::VariableOfTypeMarked,
            VariableIntro::VariableSourceOf(_) =>  Template::VariableSourceOf,
        }
    }
}

impl<'a> From<Relation<'a>> for Template {
    fn from(value: Relation<'a>) -> Self {
        match value {
            Relation::FlowsTo(_) => Template::FlowsTo,
            Relation::NoFlowsTo(_) => Template::NoFlowsTo,
            Relation::ControlFlow(_) => Template::ControlFlow,
            Relation::NoControlFlow(_) => Template::NoControlFlow,
            Relation::OnlyVia(_) => Template::OnlyVia,
            Relation::AssociatedCallSite(_) => Template::AssociatedCallSite,
            Relation::IsMarked(_) => Template::IsMarked,
            Relation::IsNotMarked(_) => Template::IsNotMarked,
            Relation::Influences(_) => Template::Influences,
            Relation::DoesNotInfluence(_) => Template::DoesNotInfluence,
        }
    }
}

impl From<Operator> for Template {
    fn from(value: Operator) -> Self {
        match value {
            Operator::And => Template::And,
            Operator::Or => Template::Or,
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

impl<'a> From<PolicyScope<'a>> for Template {
    fn from(value: PolicyScope<'a>) -> Self {
        match value {
            PolicyScope::Always => Template::Always,
            PolicyScope::Sometimes => Template::Sometimes,
            PolicyScope::InCtrler(_) => Template::InCtrler,
        }
    }
}

impl<'a> From<ClauseIntro<'a>> for Template {
    fn from(value: ClauseIntro<'a>) -> Self {
        match value {
            ClauseIntro::ForEach(_) => Template::ForEach,
            ClauseIntro::ThereIs(_) => Template::ForEach,
            ClauseIntro::Conditional(_) => Template::Conditional,
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

    let (remainder, (option_defs, (scope, body))) = combinator(s)?;
    Ok((remainder, Policy {definitions: option_defs.unwrap_or_default(), scope, body}))
}

pub mod common;
pub mod clause;
pub mod definitions;
pub mod policy_body;
pub mod relations;
pub mod scope;
pub mod variable_intro;