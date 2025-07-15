use std::collections::HashSet;

use nom::{
    branch::alt,
    bytes::complete::{tag, take_while1},
    character::complete::{alpha1, digit1, multispace0, multispace1, space0, space1},
    combinator::{opt, recognize},
    error::{context, VerboseError},
    multi::many1,
    sequence::{delimited, preceded, terminated, tuple},
    Parser,
};

use crate::common::ast::*;

use super::Res;

pub fn colon(s: &str) -> Res<&str, &str> {
    context("colon", delimited(space0, tag(":"), multispace0))(s)
}

pub fn and(s: &str) -> Res<&str, &str> {
    context("and", delimited(multispace0, tag("and"), multispace1))(s)
}

pub fn or(s: &str) -> Res<&str, &str> {
    context("or", delimited(multispace0, tag("or"), multispace1))(s)
}

pub fn operator(s: &str) -> Res<&str, Operator> {
    let mut combinator = context("operator", alt((and, or)));
    let (remainder, operator_str) = combinator(s)?;
    Ok((remainder, operator_str.into()))
}

pub fn l1_bullet(s: &str) -> Res<&str, &str> {
    context(
        "l1 bullet",
        delimited(multispace0, digit1, tuple((tag("."), space1))),
    )(s)
}

pub fn l2_bullet(s: &str) -> Res<&str, &str> {
    let uppercase = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    context(
        "l2 bullet",
        delimited(
            multispace0,
            take_while1(|c| uppercase.contains(c)),
            tuple((tag("."), space1)),
        ),
    )(s)
}

pub fn l3_bullet(s: &str) -> Res<&str, &str> {
    let lowercase = "abcdefghijklmnopqrstuvwxyz";
    context(
        "l3 bullet",
        delimited(
            multispace0,
            take_while1(|c| lowercase.contains(c)),
            tuple((tag("."), space1)),
        ),
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
            tuple((tag(")"), space1)),
        ),
    )(s)
}

pub fn l5_bullet(s: &str) -> Res<&str, &str> {
    let uppercase = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    context(
        "l5 bullet",
        delimited(
            multispace0,
            take_while1(|c| uppercase.contains(c)),
            tuple((tag(")"), space1)),
        ),
    )(s)
}

pub fn alphabetic_with_underscores(s: &str) -> Res<&str, String> {
    let mut combinator = context(
        "alphabetic with underscores",
        preceded(space0, recognize(many1(tuple((alpha1, opt(tag("_"))))))),
    );
    let (remainder, res) = combinator(s)?;
    Ok((remainder, String::from(res)))
}

pub fn marker(s: &str) -> Res<&str, Marker> {
    context(
        "marker",
        terminated(alphabetic_with_underscores, multispace0),
    )(s)
}

pub fn variable(s: &str) -> Res<&str, Variable> {
    context(
        "variable",
        delimited(
            tuple((space0, tag("\""))),
            alphabetic_with_underscores,
            tuple((tag("\""), space0)),
        ),
    )(s)
}

pub fn join_variable_intros(
    tup: (VariableIntro, Vec<(Operator, VariableIntro)>),
) -> (Option<Operator>, Vec<VariableIntro>) {
    let mut ops: HashSet<&Operator> = HashSet::new();
    for (op, _) in &tup.1 {
        ops.insert(op);
    }

    assert!(
        ops.len() <= 1,
        "Ambigious policy: cannot mix ands/ors on the same level"
    );

    let mut op = None;
    let mut vec = vec![tup.0];

    if !tup.1.is_empty() {
        for (operator, intro) in tup.1 {
            op = Some(operator);
            vec.push(intro)
        }
    }
    (op, vec)
}

// Given an initial node and a vector of (operator, node) pairs, construct an ASTNode::{Operator}
// joining each of the nodes
pub fn join_nodes((start, rest): (ASTNode, Vec<(Operator, ASTNode)>)) -> ASTNode {
    let Some(reference_op) = rest.first().map(|(op, _)| op.clone()) else {
        return start;
    };

    rest.into_iter().fold(start, |acc, (op, clause)| {
        if op != reference_op {
            panic!("Ambigious policy: cannot mix ands/ors on the same level")
        }
        let ob = TwoNodeObligation {
            op,
            src: acc,
            sink: clause,
        };
        ASTNode {
            ty: ASTNodeType::JoinedNodes(Box::new(ob)),
            span: "".to_owned(),
            clause_num: "".to_owned(),
        }
    })
}

pub fn spanned<'a, T>(
    mut parser: impl Parser<&'a str, T, VerboseError<&'a str>>,
) -> impl FnMut(&'a str) -> Res<&'a str, (T, &'a str)> {
    move |s| {
        let (remainder, result) = parser.parse(s)?;
        let span = &s[..s.len() - remainder.len()];
        Ok((remainder, (result, span)))
    }
}
