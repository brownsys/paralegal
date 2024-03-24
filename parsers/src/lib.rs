use definitions::parse_definitions;
use nom::{IResult, error::{VerboseError, context}, combinator::{all_consuming, opt}, sequence::tuple};
use policy_body::parse_policy_body;
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
    Always,
    Sometimes,
    InCtrler(String)
}

#[derive(Debug, PartialEq, Eq)]
pub struct Definition {
    // quantifier is always "all" bc definitions are over *each* var that satisifes condition
    variable: Variable,
    declaration: VariableIntro,
    filter: ASTNode
}

// AST data
#[derive(Debug, PartialEq, Eq)]
pub enum VariableIntro {
    Roots,
    Variable(Variable),
    VariableMarked((Variable, Marker)),
    VariableOfTypeMarked((Variable, Marker)),
    VariableSourceOf((Variable, Variable))
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
    OnlyVia((VariableIntro, VariableIntro, VariableIntro))
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
            &VariableIntro::Roots => Template::Roots,
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
            &Relation::OnlyVia(_) => Template::OnlyVia,
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

impl From<&PolicyScope> for Template {
    fn from(value: &PolicyScope) -> Self {
        match value {
            &PolicyScope::Always => Template::Always,
            &PolicyScope::Sometimes => Template::Sometimes,
            &PolicyScope::InCtrler(_) => Template::InCtrler,
        }
    }
}

impl From<&ClauseIntro> for Template {
    fn from(value: &ClauseIntro) -> Self {
        match value {
            &ClauseIntro::ForEach(_) => Template::ForEach,
            &ClauseIntro::ThereIs(_) => Template::ForEach,
            &ClauseIntro::Conditional(_) => Template::Conditional,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TwoNodeObligation {
    pub op: Operator,
    pub src: ASTNode,
    pub dest: ASTNode,
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
    Clause(Box<Clause>),
    JoinedNodes(Box<TwoNodeObligation>)
}

pub fn parse(s: &str) -> Res<&str, Policy> {
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