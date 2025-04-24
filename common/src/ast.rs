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
    pub filter: Option<ASTNode>,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Relation {
    Binary {
        left: Variable,
        right: Variable,
        typ: Binop,
    },
    Negation(Box<Relation>),
    IsMarked(Variable, Marker),
}

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwoNodeObligation {
    pub op: Operator,
    pub src: ASTNode,
    pub sink: ASTNode,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClauseIntro {
    ForEach(VariableIntro),
    ThereIs(VariableIntro),
    Conditional(Relation),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clause {
    pub intro: ClauseIntro,
    pub body: ASTNode,
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
