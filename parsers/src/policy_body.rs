use nom::{error::context, branch::alt, sequence::{tuple, pair, preceded, terminated}, multi::many0, combinator::map, character::complete::multispace0};
use crate::{Res, scope::scope, clause::l1_clauses, common::*, relations::only_via_relation, ASTNode, PolicyScope};

fn only_vias(s: &str) -> Res<&str, ASTNode> { 
    context(
        "multiple only via",
        map(
            pair(
                preceded(l1_bullet, map(only_via_relation, |rel| ASTNode::Relation(rel))), 
                many0(tuple((operator, preceded(l1_bullet, map(only_via_relation, |rel| ASTNode::Relation(rel))))))
            ),
            join_nodes
        )
    )(s)
}

pub fn parse_policy_body(s: &str) -> Res<&str, (PolicyScope, ASTNode)> {
    context(
        "policy body", 
        terminated(tuple((scope, alt((only_vias, l1_clauses)))), multispace0)
    )(s)
}