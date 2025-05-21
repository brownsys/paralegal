// definitions are controller-specific by default, but can be specified to be anywhere in the application
// usually, controller-specific is what you would want
// I added "Everywhere" support for the websubmit deletion policy, which reasons about all sensitive types that are stored anywhere in the application
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefinitionScope {
    Ctrler,
    Everywhere,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Definition {
    // quantifier is everywhere "all" bc definitions are over *each* var that satisifes condition
    pub variable: Variable,
    pub scope: DefinitionScope,
    pub declaration: VariableIntro,
    // filter.is_none() iff this is a lifted definition, i.e. not a definition originally but one
    // we derived through optimizations
    pub filter: Option<ASTNode>,
    // if this is a lifted definition, was it lifted from a ForEach or ThereIs clause?
    pub lifted_from: Option<OgClauseIntroType>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VariableIntro {
    pub variable: Variable,
    pub intro: VariableIntroType,
}

// AST data
#[derive(Clone, Debug, PartialEq, Eq, Hash, strum_macros::Display)]
pub enum VariableIntroType {
    Roots,
    AllNodes,
    Variable,
    VariableMarked { marker: Marker, on_type: bool },
    VariableSourceOf(Variable),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Relation {
    Binary {
        left: Variable,
        right: Variable,
        typ: Binop,
    },
    Negation(Box<Relation>),
    IsMarked(Variable, Marker),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Binop {
    Data,
    Control,
    Both,
    AssociatedCallSite,
}

pub type Variable = String;
pub type Marker = String;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Operator {
    And,
    Or,
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TwoNodeObligation {
    pub op: Operator,
    pub src: ASTNode,
    pub sink: ASTNode,
}

// Only used for optimization logic
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum OgClauseIntroType {
    Conditional,
    ForEach,
    ThereIs,
}

impl From<&ClauseIntro> for OgClauseIntroType {
    fn from(value: &ClauseIntro) -> Self {
        match value {
            ClauseIntro::ForEach(_) => OgClauseIntroType::ForEach,
            ClauseIntro::ThereIs(_) => OgClauseIntroType::ThereIs,
            ClauseIntro::Conditional(_) => OgClauseIntroType::Conditional,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ClauseIntro {
    ForEach(VariableIntro),
    ThereIs(VariableIntro),
    Conditional(Relation),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Clause {
    pub intro: ClauseIntro,
    pub body: ASTNode,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Position {
    Source,
    Target,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ASTNode {
    Clause(Box<Clause>),
    OnlyVia(
        VariableIntro,
        (Option<Operator>, Vec<VariableIntro>),
        (Option<Operator>, Vec<VariableIntro>),
    ),
    JoinedNodes(Box<TwoNodeObligation>),
    Relation(Relation),
}
