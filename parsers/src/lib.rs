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
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum VariableIntro<'a> {
    Roots,
    Variable(Variable<'a>),
    VariableMarked((Variable<'a>, Marker<'a>)),
    VariableOfTypeMarked((Variable<'a>, Marker<'a>)),
    VariableSourceof((Variable<'a>, Variable<'a>))
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Relation<'a> {
    Influences((Variable<'a>, Variable<'a>)),
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

impl From<&str> for Operator {
    fn from(s: &str) -> Self {
        match s {
            "and" => Operator::And,
            "or" => Operator::Or,
            &_ => unimplemented!("no other operators supported"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct TwoNodeObligation<'a> {
    src: ASTNode<'a>,
    dest: ASTNode<'a>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum ClauseIntro<'a> {
    ForEach(VariableIntro<'a>),
    ThereIs(VariableIntro<'a>),
    Conditional(Relation<'a>)
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Clause<'a> {
    intro: ClauseIntro<'a>,
    body: ASTNode<'a>
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum ASTNode<'a> {
    Relation(Relation<'a>),
    And(Box<TwoNodeObligation<'a>>),
    Or(Box<TwoNodeObligation<'a>>),
    Conditional(Box<TwoNodeObligation<'a>>),
    Clause(Box<Clause<'a>>)
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