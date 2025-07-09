use crate::{
    relations::*,
    shared::*,
    variable_intro::{variable_def, variable_intro, variable_marked},
    Res,
};
use common::ast::*;
use nom::{
    branch::alt,
    character::complete::space1,
    combinator::map,
    multi::many0,
    sequence::{delimited, pair, preceded, tuple},
};

use nom_supreme::tag::complete::tag;

fn l4_clause(s: &str) -> Res<&str, ASTNode> {
    let mut combinator = tuple((
        preceded(l4_bullet, alt((for_each, there_is, conditional))),
        l5_relations,
    ));
    let (remainder, (intro, body)) = combinator(s)?;
    Ok((remainder, ASTNode::Clause(Box::new(Clause { intro, body }))))
}

pub fn l4_clauses(s: &str) -> Res<&str, ASTNode> {
    map(
        pair(
            l4_clause,
            many0(pair(operator, alt((l4_clause, l4_relations)))),
        ),
        join_nodes,
    )(s)
}

fn l3_clause(s: &str) -> Res<&str, ASTNode> {
    let mut combinator = tuple((
        preceded(l3_bullet, alt((for_each, there_is, conditional))),
        alt((l4_relations, l4_clauses)),
    ));
    let (remainder, (intro, body)) = combinator(s)?;
    Ok((remainder, ASTNode::Clause(Box::new(Clause { intro, body }))))
}

pub fn l3_clauses(s: &str) -> Res<&str, ASTNode> {
    map(
        pair(
            l3_clause,
            many0(pair(operator, alt((l3_clause, l3_relations)))),
        ),
        join_nodes,
    )(s)
}

fn l2_clause(s: &str) -> Res<&str, ASTNode> {
    let mut combinator = tuple((
        preceded(l2_bullet, alt((for_each, there_is, conditional))),
        alt((l3_relations, l3_clauses)),
    ));
    let (remainder, (intro, body)) = combinator(s)?;
    Ok((remainder, ASTNode::Clause(Box::new(Clause { intro, body }))))
}

pub fn l2_clauses(s: &str) -> Res<&str, ASTNode> {
    map(
        pair(
            l2_clause,
            many0(pair(operator, alt((l2_clause, l2_relations)))),
        ),
        join_nodes,
    )(s)
}

fn l1_clause(s: &str) -> Res<&str, ASTNode> {
    let mut combinator = tuple((
        preceded(l1_bullet, alt((for_each, there_is))),
        alt((l2_relations, l2_clauses)),
    ));
    let (remainder, (intro, body)) = combinator(s)?;
    Ok((remainder, ASTNode::Clause(Box::new(Clause { intro, body }))))
}

pub fn l1_clauses(s: &str) -> Res<&str, ASTNode> {
    map(
        pair(
            alt((l1_clause, only_via)),
            many0(tuple((operator, alt((l1_clause, only_via))))),
        ),
        join_nodes,
    )(s)
}

fn only_via(s: &str) -> Res<&str, ASTNode> {
    let mut combinator = tuple((
        // these are only allowed to be present at the top level, hence the L1 bullet restriction
        delimited(
            tuple((l1_bullet, tag("Each"), space1)),
            variable_intro,
            tag("goes to a"),
        ),
        map(
            pair(
                alt((variable_marked, variable_def)),
                many0(tuple((operator, alt((variable_marked, variable_def))))),
            ),
            join_variable_intros,
        ),
        preceded(
            tag("only via a"),
            map(
                pair(
                    alt((variable_marked, variable_def)),
                    many0(tuple((operator, alt((variable_marked, variable_def))))),
                ),
                join_variable_intros,
            ),
        ),
    ));
    let (remainder, (src, sink, checkpoint)) = combinator(s)?;

    Ok((remainder, ASTNode::OnlyVia(src, sink, checkpoint)))
}

fn conditional(s: &str) -> Res<&str, ClauseIntro> {
    let mut combinator = delimited(tag("If"), relation, tuple((tag("then"), colon)));
    let (remainder, relation) = combinator(s)?;
    Ok((remainder, ClauseIntro::Conditional(relation)))
}

fn for_each(s: &str) -> Res<&str, ClauseIntro> {
    let mut combinator = delimited(tuple((tag("For each"), space1)), variable_intro, colon);
    let (remainder, var_intro) = combinator(s)?;
    Ok((remainder, ClauseIntro::ForEach(var_intro)))
}

fn there_is(s: &str) -> Res<&str, ClauseIntro> {
    let mut combinator = delimited(tag("There is a"), variable_intro, tag("where:"));
    let (remainder, var_intro) = combinator(s)?;
    Ok((remainder, ClauseIntro::ThereIs(var_intro)))
}
