use nom::{
    branch::alt,
    bytes::complete::{tag, take_while1},
    character::complete::{alpha1, space0, space1, multispace0, multispace1, digit1},
    combinator::{opt, recognize},
    error::context,
    multi::many1,
    sequence::{delimited, terminated, tuple, preceded},
};

use crate::{
    Marker, Operator, Variable, Res, ASTNode, TwoNodeObligation
};

pub fn colon(s: &str) -> Res<&str, &str> {
    context("colon", delimited(space0, tag(":"), multispace0))(s)
}

pub fn and(s: &str) -> Res<&str, &str> {
    context("and", delimited(multispace0, tag("and"), multispace1))(s)
}

pub fn or(s: &str) -> Res<&str, &str> {
    context("or", delimited(multispace0, tag("or"), multispace1))(s)
}

pub fn operator<'a>(s: &'a str) -> Res<&str, Operator> {
    let mut combinator = context("operator", alt((and, or)));
    let (remainder, operator_str) = combinator(s)?;
    Ok((remainder, operator_str.into()))
}

pub fn l1_bullet(s: &str) -> Res<&str, &str> {
    context(
        "l1 bullet",
        delimited(
            multispace0,
            digit1, 
            tuple((tag("."), space1))
        )
    )(s)
}

pub fn l2_bullet(s: &str) -> Res<&str, &str> {
    let uppercase = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    context(
        "l2 bullet",
        delimited(
            multispace0,
            take_while1(|c| uppercase.contains(c)),
            tuple((tag("."), space1))
        )
    )(s)
}

pub fn l3_bullet(s: &str) -> Res<&str, &str> {
    let lowercase = "abcdefghijklmnopqrstuvwxyz";
    context(
        "l3 bullet",
        delimited(
            multispace0,
            take_while1(|c| lowercase.contains(c)),
            tuple((tag("."), space1))
        )
    )(s)
}

pub fn l4_bullet(s: &str) -> Res<&str, &str> {
    // todo: this is lazy, write a real roman numeral parser later
    let roman = "ixv";
    context(
        "l4 bullet",
        delimited(
            multispace0,
            take_while1(|c| roman.contains(c)),
            // terminate with ) to avoid ambiguity with l3 bullet lowercase i
            tuple((tag(")"), space1))
        )
    )(s)
}

pub fn l5_bullet(s: &str) -> Res<&str, &str> {
    let uppercase = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    context(
        "l5 bullet",
        delimited(
            multispace0,
            take_while1(|c| uppercase.contains(c)),
            tuple((tag(")"), space1))
        )
    )(s)
}

pub fn alphabetic_with_underscores<'a>(s: &'a str) -> Res<&str, Marker<'a>> {
    context(
        "alphabetic with underscores",
        preceded(
            space0,
            recognize(
                many1(
                    tuple((alpha1, opt(tag("_"))))
                )
            ),
        )
    )(s)
}

pub fn marker<'a>(s: &'a str) -> Res<&str, Marker<'a>> {
    context(
        "marker",
        terminated(
            alphabetic_with_underscores,
            multispace0
        )
    )(s)
}

pub fn variable<'a>(s: &'a str) -> Res<&str, Variable<'a>> {
    context(
        "variable",
        alt((
            delimited(
                tuple((space0, tag("\""))),
                alphabetic_with_underscores,
                tuple((tag("\""), space0)), 
            ),
            delimited(
                tuple((space0, tag("\""))),
                recognize(many1(tuple((alpha1, opt(space1))))),
                tuple((tag("\""), space0)), 
            )
        ))   
    )(s)
}

// Given an initial node and a vector of (operator, node) pairs, construct an ASTNode::{Operator}
// joining each of the nodes
// TODO add assertion that each operator in the vector is the same (can't mix ands & ors)
pub fn join_nodes<'a>(tup: (ASTNode<'a>, Vec<(Operator, ASTNode<'a>)>)) -> ASTNode<'a> {
    tup.1
    .into_iter()
    .fold(tup.0, |acc, (op, clause)| {
        let ob = TwoNodeObligation {
            op,
            src: acc,
            dest: clause
        };
        ASTNode::JoinedNodes(Box::new(ob))
    })
}
