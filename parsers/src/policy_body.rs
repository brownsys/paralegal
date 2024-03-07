use nom::{
    branch::alt,
    error::context,
    sequence::{tuple, delimited, preceded}, character::complete::{space0, multispace0}, bytes::complete::tag,
};

use crate::{
    ASTNode, PolicyBody, PolicyScope, Res, common::*, variable_clause::variable_clause, relations::only_via_relation, TwoNodeObligation, Operator,
};

fn outer_multiple_variable_clauses<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "multiple clauses",
        tuple((
            variable_clause,
            operator,
            exprs,
        )),
    );
    // TODO the logic below is repeated in multiple parsers
    // would be nice to abstract it into a function, but when I tried the compiler yelled at me about the lifetime of s
    // and I couldn't fix it after a couple minutes so I left it as-is for now
    let (remainder, (src, operator, dest)) = combinator(s)?;
    let body = Box::new(TwoNodeObligation {src, dest});

    let node = match operator {
        Operator::And => ASTNode::And(body),
        Operator::Or => ASTNode::Or(body),
    };

    Ok((remainder, node))
}

pub fn multiple_only_via_relation<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "multiple only via relation",
        tuple((
            preceded(bullet, only_via_relation),
            operator, 
            alt((preceded(bullet, only_via_relation), multiple_only_via_relation))
        ))
    );
    let (remainder, (src, operator, dest)) = combinator(s)?;
    let body = Box::new(TwoNodeObligation {src, dest});

    let node = match operator {
        Operator::And => ASTNode::And(body),
        Operator::Or => ASTNode::Or(body),
    };

    Ok((remainder, node))
}

pub fn exprs<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    context(
        "exprs",
        alt((
            // TODO there must be a more elegant way of doing this only via handling
            multiple_only_via_relation,
            preceded(bullet, only_via_relation),
            outer_multiple_variable_clauses,
            variable_clause, 
        ))
    )(s)
}

pub fn always(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context(
        "always",
        tuple((multispace0, tag("always"), colon)),
    );
    let (remainder, _) = combinator(s)?;
    Ok((remainder, PolicyScope::Always))
}

pub fn sometimes(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context(
        "sometimes",
        tuple((multispace0, tag("sometimes"), colon)),
    );
    let (remainder, _) = combinator(s)?;
    Ok((remainder, PolicyScope::Sometimes))
}

pub fn in_ctrler<'a>(s: &'a str) -> Res<&str, PolicyScope<'a>> {
    let mut combinator = context(
        "in ctrler",
        delimited(
            tuple((multispace0, tag("in"))),
            alphabetic_with_underscores, 
            colon,
        )
    );
    let (remainder, ctrler) = combinator(s)?;
    Ok((remainder, PolicyScope::InCtrler(ctrler)))
}

pub fn scope(s: &str) -> Res<&str, PolicyScope> {
    context("scope", 
        alt((always, sometimes, in_ctrler))
    )(s)
}

pub fn parse_policy_body<'a>(s: &'a str) -> Res<&str, PolicyBody<'a>> {
    let mut combinator = context(
        "policy body", 
        tuple((scope, exprs))
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