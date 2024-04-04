use clause::l1_clauses;
use definitions::parse_definitions;
use scope::scope;
use nom::{IResult, error::{VerboseError, context}, combinator::{all_consuming, opt}, sequence::{tuple, terminated}, character::complete::multispace0};
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
    InCtrler(String)
}

#[derive(Debug, PartialEq, Eq)]
pub struct Definition {
    // quantifier is everywhere "all" bc definitions are over *each* var that satisifes condition
    pub variable: Variable,
    pub declaration: VariableIntro,
    pub filter: ASTNode
}

// AST data
#[derive(Debug, PartialEq, Eq)]
pub enum VariableIntro {
    Roots(Variable),
    AllNodes(Variable),
    Variable(Variable),
    VariableMarked((Variable, Marker)),
    VariableOfTypeMarked((Variable, Marker)),
    VariableSourceOf((Variable, Variable)),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Relation {
    Influences((Variable, Variable)),
    DoesNotInfluence((Variable, Variable)),
    FlowsTo((Variable, Variable)),
    NoFlowsTo((Variable, Variable)),
    ControlFlow((Variable, Variable)),
    NoControlFlow((Variable, Variable)),
    AssociatedCallSite((Variable, Variable)),
    IsMarked((Variable, Marker)),
    IsNotMarked((Variable, Marker)),
}

pub type Variable = String;
pub type Marker = String;

#[derive(Debug, PartialEq, Eq)]
pub enum Operator {
    And,
    Or,
}

// map templates to their handlebars template file names
impl From<&VariableIntro> for Template {
    fn from(value: &VariableIntro) -> Self {
        match value {
            &VariableIntro::Roots(_) => Template::Roots,
            &VariableIntro::AllNodes(_) => Template::AllNodes,
            &VariableIntro::Variable(_) => Template::Variable,
            &VariableIntro::VariableMarked(_) => Template::VariableMarked,
            &VariableIntro::VariableOfTypeMarked(_) => Template::VariableOfTypeMarked,
            &VariableIntro::VariableSourceOf(_) =>  Template::VariableSourceOf,
        }
    }
}

impl From<&Relation> for Template {
    fn from(value: &Relation) -> Self {
        match value {
            &Relation::FlowsTo(_) => Template::FlowsTo,
            &Relation::NoFlowsTo(_) => Template::NoFlowsTo,
            &Relation::ControlFlow(_) => Template::ControlFlow,
            &Relation::NoControlFlow(_) => Template::NoControlFlow,
            &Relation::AssociatedCallSite(_) => Template::AssociatedCallSite,
            &Relation::IsMarked(_) => Template::IsMarked,
            &Relation::IsNotMarked(_) => Template::IsNotMarked,
            &Relation::Influences(_) => Template::Influences,
            &Relation::DoesNotInfluence(_) => Template::DoesNotInfluence,
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
            _ => unimplemented!("invalid operator: valid options are 1) and 2) or")
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
            ASTNode::OnlyVia(_) => Template::OnlyVia,
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
    Conditional(Relation)
}

#[derive(Debug, PartialEq, Eq)]
pub struct Clause {
    pub intro: ClauseIntro,
    pub body: ASTNode
}

#[derive(Debug, PartialEq, Eq)]
pub enum ASTNode {
    Relation(Relation),
    OnlyVia((VariableIntro, VariableIntro, VariableIntro)),
    Clause(Box<Clause>),
    JoinedNodes(Box<TwoNodeObligation>),
}

pub fn parse(s: &str) -> Res<&str, Policy> {
    let mut combinator = context(
        "parse policy", 
        all_consuming(
            tuple((opt(parse_definitions), terminated(tuple((scope, l1_clauses)), multispace0)))
        )
    );

    let (remainder, (option_defs, (scope, body))) = combinator(s)?;
    Ok((remainder, Policy {definitions: option_defs.unwrap_or_default(), scope, body}))
}

pub mod common;
pub mod clause;
pub mod definitions;
pub mod relations;
pub mod scope;
pub mod variable_intro;