use super::{
    relations::*,
    shared::*,
    variable_intro::{variable_def, variable_intro, variable_marked},
    Res,
};
use crate::common::ast::*;
use nom::{
    branch::alt,
    character::complete::space1,
    combinator::map,
    multi::many0,
    sequence::{delimited, pair, preceded, terminated, tuple},
    Parser,
};

use nom_supreme::{error::ErrorTree, tag::complete::tag};

fn gclause<'a>(
    bullet: impl Parser<&'a str, &'a str, ErrorTree<&'a str>>,
    intro: impl Parser<&'a str, (ClauseIntro, &'a str), ErrorTree<&'a str>>,
    remainder: impl Parser<&'a str, ASTNode, ErrorTree<&'a str>>,
) -> impl FnMut(&'a str) -> Res<&'a str, ASTNode> {
    map(
        tuple((bullet, intro, remainder)),
        |(bullet, (intro, ispan), body)| ASTNode {
            clause_num: bullet.to_owned(),
            span: ispan.to_owned(),
            ty: ASTNodeType::Clause(Box::new(Clause { intro, body })),
        },
    )
}

fn l4_clause(s: &str) -> Res<&str, ASTNode> {
    gclause(
        l4_bullet,
        alt((for_each, there_is, conditional)),
        l5_relations,
    )(s)
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
    gclause(
        l3_bullet,
        alt((for_each, there_is, conditional)),
        alt((l4_relations, l4_clauses)),
    )(s)
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
    gclause(
        l2_bullet,
        alt((for_each, there_is, conditional)),
        alt((l3_relations, l3_clauses)),
    )(s)
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
    gclause(
        l1_bullet,
        alt((for_each, there_is)),
        alt((l2_relations, l2_clauses)),
    )(s)
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
    let intro = &|s| {
        map(
            pair(
                alt((variable_marked, variable_def)),
                many0(tuple((operator, alt((variable_marked, variable_def))))),
            ),
            join_variable_intros,
        )(s)
    };
    let mut combinator = tuple((
        // these are only allowed to be present at the top level, hence the
        // L1 bullet restriction
        l1_bullet,
        spanned(tuple((
            delimited(
                tuple((tag("Each"), space1)),
                variable_intro,
                tag("goes to a"),
            ),
            intro,
            preceded(tag("only via a"), intro),
        ))),
    ));
    let (remainder, (bullet, ((src, sink, checkpoint), span))) = combinator(s)?;

    Ok((
        remainder,
        ASTNode {
            clause_num: bullet.to_owned(),
            span: span.to_owned(),
            ty: ASTNodeType::OnlyVia(src, sink, checkpoint),
        },
    ))
}

fn conditional(s: &str) -> Res<&str, (ClauseIntro, &str)> {
    map(
        terminated(spanned(delimited(tag("If"), relation, tag("then"))), colon),
        |(a, span)| (ClauseIntro::Conditional(a), span),
    )(s)
}

fn for_each(s: &str) -> Res<&str, (ClauseIntro, &str)> {
    map(
        terminated(
            spanned(preceded(tuple((tag("For each"), space1)), variable_intro)),
            colon,
        ),
        |(a, span)| (ClauseIntro::ForEach(a), span),
    )(s)
}

fn there_is(s: &str) -> Res<&str, (ClauseIntro, &str)> {
    map(
        terminated(
            spanned(delimited(tag("There is a"), variable_intro, tag("where"))),
            colon,
        ),
        |(a, span)| (ClauseIntro::ThereIs(a), span),
    )(s)
}
