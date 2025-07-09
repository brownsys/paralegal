use common::ast::*;
use nom::{
    branch::alt,
    character::complete::{space0, space1},
    combinator::{map, peek},
    error::context,
    multi::many0,
    sequence::{pair, preceded, separated_pair, terminated, tuple},
};
use nom_supreme::tag::complete::tag;

use crate::{shared::*, Res};

// this is flows_to(EdgeSelection::DataAndControl)
fn influences_relation(s: &str) -> Res<&str, Relation> {
    let mut combinator = separated_pair(variable, tuple((tag("influences"), space1)), variable);
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        Relation::Binary {
            left: var1,
            right: var2,
            typ: Binop::Both,
        },
    ))
}

fn does_not_influence_relation(s: &str) -> Res<&str, Relation> {
    let mut combinator = separated_pair(
        variable,
        tuple((tag("does not influence"), space1)),
        variable,
    );
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        Relation::Negation(Box::new(Relation::Binary {
            left: var1,
            right: var2,
            typ: Binop::Both,
        })),
    ))
}

// this is flows_to(EdgeSelection::Data)
fn goes_to_relation(s: &str) -> Res<&str, Relation> {
    let mut combinator = separated_pair(variable, tuple((tag("goes to"), space1)), variable);
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        Relation::Binary {
            left: var1,
            right: var2,
            typ: Binop::Data,
        },
    ))
}

fn does_not_go_to_relation(s: &str) -> Res<&str, Relation> {
    let mut combinator = separated_pair(variable, tag("does not go to"), variable);
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        Relation::Negation(Box::new(Relation::Binary {
            left: var1,
            right: var2,
            typ: Binop::Data,
        })),
    ))
}

fn operation_associated_with_relation(s: &str) -> Res<&str, Relation> {
    let mut combinator = pair(
        terminated(variable, tag("goes to")),
        terminated(variable, tag("'s operation")),
    );
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        Relation::Binary {
            left: var1,
            right: var2,
            typ: Binop::AssociatedCallSite,
        },
    ))
}

fn affects_whether_relation(s: &str) -> Res<&str, Relation> {
    let mut combinator = tuple((
        terminated(variable, tag("affects whether")),
        terminated(variable, tag("happens")),
    ));
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        Relation::Binary {
            left: var1,
            right: var2,
            typ: Binop::Control,
        },
    ))
}

fn does_not_affects_whether_relation(s: &str) -> Res<&str, Relation> {
    let mut combinator = tuple((
        terminated(variable, tag("does not affect whether")),
        terminated(variable, tag("happens")),
    ));
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        Relation::Negation(Box::new(Relation::Binary {
            left: var1,
            right: var2,
            typ: Binop::Control,
        })),
    ))
}

fn is_marked_relation(s: &str) -> Res<&str, Relation> {
    let mut combinator = separated_pair(variable, tag("is marked"), marker);
    let (remainder, (var, marker)) = combinator(s)?;

    Ok((remainder, Relation::IsMarked(var, marker)))
}

fn is_not_marked_relation(s: &str) -> Res<&str, Relation> {
    let mut combinator = separated_pair(variable, tag("is not marked"), marker);
    let (remainder, (var, marker)) = combinator(s)?;

    Ok((
        remainder,
        Relation::Negation(Box::new(Relation::IsMarked(var, marker))),
    ))
}

pub fn relation(s: &str) -> Res<&str, Relation> {
    let (remainder, _) = context("a variable", tuple((space0, peek(variable))))(s)?;
    context(
        "a relation between two variables",
        alt((
            operation_associated_with_relation,
            goes_to_relation,
            does_not_go_to_relation,
            affects_whether_relation,
            does_not_affects_whether_relation,
            is_marked_relation,
            is_not_marked_relation,
            influences_relation,
            does_not_influence_relation,
        )),
    )(remainder)
}

pub fn l2_relations(s: &str) -> Res<&str, ASTNode> {
    map(
        pair(
            preceded(l2_bullet, map(relation, ASTNode::Relation)),
            many0(tuple((
                operator,
                (preceded(l2_bullet, map(relation, ASTNode::Relation))),
            ))),
        ),
        join_nodes,
    )(s)
}

pub fn l3_relations(s: &str) -> Res<&str, ASTNode> {
    map(
        pair(
            preceded(l3_bullet, map(relation, ASTNode::Relation)),
            many0(tuple((
                operator,
                (preceded(l3_bullet, map(relation, ASTNode::Relation))),
            ))),
        ),
        join_nodes,
    )(s)
}

pub fn l4_relations(s: &str) -> Res<&str, ASTNode> {
    map(
        pair(
            preceded(l4_bullet, map(relation, ASTNode::Relation)),
            many0(tuple((
                operator,
                (preceded(l4_bullet, map(relation, ASTNode::Relation))),
            ))),
        ),
        join_nodes,
    )(s)
}

pub fn l5_relations(s: &str) -> Res<&str, ASTNode> {
    map(
        pair(
            preceded(l5_bullet, map(relation, ASTNode::Relation)),
            many0(tuple((
                operator,
                (preceded(l5_bullet, map(relation, ASTNode::Relation))),
            ))),
        ),
        join_nodes,
    )(s)
}
