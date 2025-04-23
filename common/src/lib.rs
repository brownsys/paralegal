use ast::{ASTNode, Definition};

pub mod ast;
pub mod templates;

// Top-level policy / definition data
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Policy {
    pub definitions: Vec<Definition>,
    pub scope: PolicyScope,
    pub body: ASTNode,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PolicyScope {
    Everywhere,
    Somewhere,
    InCtrler(String),
}
