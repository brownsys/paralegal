use clause::l1_clauses;
use common::colon;
use definitions::parse_definitions;
use nom::{
    bytes::complete::tag,
    character::complete::multispace0,
    combinator::{all_consuming, opt},
    error::{context, VerboseError},
    sequence::{delimited, tuple},
    IResult,
};
use scope::scope;
use templates::Template;

pub type Res<T, U> = IResult<T, U, VerboseError<T>>;

// Top-level policy / definition data
#[derive(Debug, PartialEq, Eq)]
pub struct Policy {
    pub definitions: Vec<Definition>,
    pub scope: PolicyScope,
    pub body: ASTNode,
}

#[derive(Debug, PartialEq, Eq)]
pub enum PolicyScope {
    Everywhere,
    Somewhere,
    InCtrler(String),
}

// definitions are controller-specific by default, but can be specified to be anywhere in the application
// usually, controller-specific is what you would want
// I added "Everywhere" support for the websubmit deletion policy, which reasons about all sensitive types that are stored anywhere in the application
#[derive(Debug, PartialEq, Eq)]
pub enum DefinitionScope {
    Ctrler,
    Everywhere,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Definition {
    // quantifier is everywhere "all" bc definitions are over *each* var that satisifes condition
    pub variable: Variable,
    pub scope: DefinitionScope,
    pub declaration: VariableIntro,
    pub filter: ASTNode,
}

#[derive(Debug, PartialEq, Eq)]
pub struct VariableIntro {
    pub variable: Variable,
    pub intro: VariableIntroType,
}

// AST data
#[derive(Debug, PartialEq, Eq)]
pub enum VariableIntroType {
    Roots,
    AllNodes,
    Variable,
    VariableMarked { marker: Marker, on_type: bool },
    VariableSourceOf(Variable),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Relation {
    Binary {
        left: Variable,
        right: Variable,
        typ: Binop,
    },
    Negation(Box<Relation>),
    IsMarked(Variable, Marker),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Binop {
    Data,
    Control,
    Both,
    AssociatedCallSite,
}

pub type Variable = String;
pub type Marker = String;

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Operator {
    And,
    Or,
}

// map templates to their handlebars template file names
impl From<&VariableIntro> for Template {
    fn from(value: &VariableIntro) -> Self {
        use VariableIntroType::*;
        match value.intro {
            Roots => Template::Roots,
            AllNodes => Template::AllNodes,
            Variable => Template::Variable,
            VariableMarked { on_type, .. } => {
                if on_type {
                    Template::VariableOfTypeMarked
                } else {
                    Template::VariableMarked
                }
            }
            VariableSourceOf(_) => Template::VariableSourceOf,
        }
    }
}

impl From<&Relation> for Template {
    fn from(value: &Relation) -> Self {
        match &value {
            Relation::Binary { typ, .. } => match typ {
                Binop::AssociatedCallSite => Template::AssociatedCallSite,
                Binop::Data => Template::FlowsTo,
                Binop::Control => Template::ControlFlow,
                Binop::Both => Template::Influences,
            },
            Relation::IsMarked { .. } => Template::IsMarked,
            Relation::Negation(_) => Template::Negation,
        }
    }
}

impl From<&Operator> for Template {
    fn from(value: &Operator) -> Self {
        match value {
            &Operator::And => Template::And,
            &Operator::Or => Template::Or,
        }
    }
}

impl From<&str> for Operator {
    fn from(value: &str) -> Self {
        match value {
            "and" => Operator::And,
            "or" => Operator::Or,
            _ => unimplemented!("invalid operator: valid options are 1) and 2) or"),
        }
    }
}

impl From<PolicyScope> for Template {
    fn from(value: PolicyScope) -> Self {
        match value {
            PolicyScope::Everywhere => Template::Everywhere,
            PolicyScope::Somewhere => Template::Somewhere,
            PolicyScope::InCtrler(_) => Template::InCtrler,
        }
    }
}

impl From<&ClauseIntro> for Template {
    fn from(value: &ClauseIntro) -> Self {
        match value {
            &ClauseIntro::ForEach(_) => Template::ForEach,
            &ClauseIntro::ThereIs(_) => Template::ThereIs,
            &ClauseIntro::Conditional(_) => Template::Conditional,
        }
    }
}

impl From<&ASTNode> for Template {
    fn from(value: &ASTNode) -> Self {
        match value {
            ASTNode::Relation(relation) => relation.into(),
            ASTNode::OnlyVia { .. } => Template::OnlyVia,
            ASTNode::Clause(clause) => (&clause.intro).into(),
            ASTNode::JoinedNodes(obligation) => (&obligation.op).into(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TwoNodeObligation {
    pub op: Operator,
    pub src: ASTNode,
    pub sink: ASTNode,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ClauseIntro {
    ForEach(VariableIntro),
    ThereIs(VariableIntro),
    Conditional(Relation),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Clause {
    pub intro: ClauseIntro,
    pub body: ASTNode,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ASTNode {
    Relation(Relation),
    OnlyVia(
        VariableIntro,
        (Option<Operator>, Vec<VariableIntro>),
        (Option<Operator>, Vec<VariableIntro>),
    ),
    Clause(Box<Clause>),
    JoinedNodes(Box<TwoNodeObligation>),
}

pub fn parse(s: &str) -> Res<&str, Policy> {
    let mut combinator = context(
        "parse policy",
        all_consuming(tuple((
            scope,
            opt(parse_definitions),
            delimited(
                tuple((multispace0, tag("Policy"), colon)),
                l1_clauses,
                multispace0,
            ),
        ))),
    );

    let (remainder, (scope, option_defs, body)) = combinator(s)?;
    Ok((
        remainder,
        Policy {
            definitions: option_defs.unwrap_or_default(),
            scope,
            body,
        },
    ))
}

pub mod clause;
pub mod common;
pub mod definitions;
pub mod relations;
pub mod scope;
pub mod variable_intro;
