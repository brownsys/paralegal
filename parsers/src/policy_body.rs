use nom::{error::context, branch::alt, sequence::{tuple, pair, preceded}, multi::many0, combinator::map};
use crate::{Res, scope::scope, PolicyBody, clause::l1_clauses, common::*, relations::only_via_relation, ASTNode};

fn only_vias<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> { 
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

pub fn parse_policy_body<'a>(s: &'a str) -> Res<&str, PolicyBody<'a>> {
    let mut combinator = context(
        "policy body", 
        tuple((scope, alt((only_vias, l1_clauses))))
    );
    let (remainder, (scope, body)) = combinator(s)?;
    Ok((
        remainder,
        PolicyBody {
            scope,
            body
        }
    ))
}