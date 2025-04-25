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

/// Product of "fusing" a clause with an operation below it.
/// E.g., starting from:
/// For each "A" marked A
///     There is a "B" marked B where:
///         "A" goes to "B"
///         ...
/// The compiler would usually collect all the "B"s, then filter by which ones "A"s go to.
/// This indicates to the compiler that it should instead
/// collect all the items that "A" goes to, then filter by those marked B,
/// which is faster if there are many Bs.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FusedClause {
    // "A" in our example
    pub outer_var: Variable,
    pub binop: Binop,
    /// Used in combination with binop to know the position of var.
    /// E.g., for BinOp::Data, Position::Source indicates that we should fetch everything that
    /// var goes to, while Position::Target indicates we should fetch everything that goes to var.
    pub pos: Position,
    /// "There is a B marked B" in our example.
    /// We use this to filter the results of the binop, hence the name.
    pub filter: VariableIntro,
    /// Whatever was below the initial clause to begin with (the ...) in our example,
    /// i.e. the rest of the policy body.
    /// (We could call this body, but it's not really the "body" of this relation
    /// as much as whatever comes after it, which we just store here to keep the tree struture).
    /// There may not be anything after it if we just have two clauses and a relation, hence the Option.
    pub rest: Option<ASTNode>,
    // We can fuse in two situations: if we have two clauses and a relation,
    // or two clauses and a conditional. This boolean indicates which it is,
    // which is important for compilation so we know whether the relation in this clause must hold.
    pub is_conditional: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ASTNode {
    Clause(Box<Clause>),
    FusedClause(Box<FusedClause>),
    OnlyVia(
        VariableIntro,
        (Option<Operator>, Vec<VariableIntro>),
        (Option<Operator>, Vec<VariableIntro>),
    ),
    JoinedNodes(Box<TwoNodeObligation>),
    Relation(Relation),
}
