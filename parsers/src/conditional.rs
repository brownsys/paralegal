use nom::{
    branch::alt,
    bytes::complete::tag,
    error::context,
    sequence::{tuple, delimited, preceded},
};

use crate::{
    ASTNode, Res, common::*, relations::*,
    TwoNodeObligation, variable_clause::{l4_clauses, l3_clauses},
};

fn conditional_premise<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    context(
        "conditional_premise",
        delimited(tag("If"), relation, tuple((tag("then"), colon)))
    )(s)
}

pub fn l4_conditional<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "l4 conditional",
        tuple((
            preceded(l4_bullet, conditional_premise),
            l5_relations,
        ))
    );
    let (remainder, (src, dest)) = combinator(s)?;
    Ok((
        remainder,
        ASTNode::Conditional(Box::new(TwoNodeObligation {
            src,
            dest
        }))
    ))
}

pub fn l3_conditional<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "l3 conditional",
        tuple((
            preceded(l3_bullet, conditional_premise),
            alt((
                l4_relations,
                l4_clauses
            ))
        ))
    );
    let (remainder, (src, dest)) = combinator(s)?;
    Ok((
        remainder,
        ASTNode::Conditional(Box::new(TwoNodeObligation {
            src,
            dest
        }))
    ))
}

pub fn l2_conditional<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "l2 conditional",
        tuple((
            preceded(l2_bullet, conditional_premise),
            alt((
                l3_relations,
                l3_clauses
            ))
        ))
    );
    let (remainder, (src, dest)) = combinator(s)?;
    Ok((
        remainder,
        ASTNode::Conditional(Box::new(TwoNodeObligation {
            src,
            dest
        }))
    ))
}