use ast::*;

pub mod ast;
pub mod templates;
pub mod verify_scope;
pub mod vis;

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

// Count the number of times `body` references `variable`.
pub fn count_references_to_variable(variable: &Variable, body: &ASTNodeType, count: &mut u16) {
    fn relation_count(relation: &Relation, variable: &Variable, count: &mut u16) {
        match relation {
            Relation::Binary {
                left,
                right,
                typ: _,
            } => {
                if left == variable {
                    *count += 1;
                }
                if right == variable {
                    *count += 1;
                }
            }
            Relation::IsMarked(var, _) => {
                if var == variable {
                    *count += 1;
                }
            }
            Relation::Negation(relation) => relation_count(relation, variable, count),
        }
    }

    match body {
        ASTNodeType::Relation(relation) => relation_count(relation, variable, count),
        ASTNodeType::Clause(clause) => {
            match &clause.intro {
                ClauseIntro::ForEach(intro) | ClauseIntro::ThereIs(intro) => {
                    if intro.variable == *variable {
                        *count += 1;
                    }
                }
                ClauseIntro::Conditional(relation) => relation_count(relation, variable, count),
            }
            count_references_to_variable(variable, &clause.body.ty, count);
        }
        ASTNodeType::JoinedNodes(obligation) => {
            count_references_to_variable(variable, &obligation.src.ty, count);
            count_references_to_variable(variable, &obligation.sink.ty, count);
        }
        ASTNodeType::OnlyVia(..) => unreachable!("Only via can't be inside another clause."),
    }
}
