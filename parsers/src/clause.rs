use nom::{
    branch::alt,
    bytes::complete::tag,
    error::context,
    sequence::{tuple, delimited, preceded, pair}, character::complete::space1, multi::many0, combinator::map,
};

use crate::{
    ASTNode, Res, common::*, relations::*,
    variable_intro::variable_intro, Clause, ClauseIntro,
};

fn l4_clause<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "l4 clause",
        tuple((
            preceded(l4_bullet, alt((for_each, there_is, conditional))),
            l5_relations,
        ))
    );
    let (remainder, (intro, body)) = combinator(s)?;
    Ok((
        remainder,
        ASTNode::Clause(Box::new(Clause {
            intro,
            body
        }))
    ))
}

pub fn l4_clauses<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> { 
    context(
        "multiple l4 clauses",
        map(
            pair(
                l4_clause, 
                many0(pair(operator, alt((l4_clause, l4_relations))))
            ),
            join_nodes
        )
    )(s)
}

fn l3_clause<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "l3 clause",
        tuple((
            preceded(l3_bullet, alt((for_each, there_is, conditional))),
            alt((
                l4_relations,
                l4_clauses
            ))
        ))
    );
    let (remainder, (intro, body)) = combinator(s)?;
    Ok((
        remainder,
        ASTNode::Clause(Box::new(Clause {
            intro,
            body
        }))
    ))
}

pub fn l3_clauses<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> { 
    context(
        "multiple l3 clauses",
        map(
            pair(
                l3_clause, 
                many0(pair(operator, alt((l3_clause, l3_relations))))
            ),
            join_nodes
        )
    )(s)
}

fn l2_clause<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "l2 clause",
        tuple((
            preceded(l2_bullet, alt((for_each, there_is, conditional))),
            alt((
                l3_relations,
                l3_clauses,
                // join nodes of pair(alt((relation, clause, many0(pair(operator, alt((l3_clause, l3_relations))))
            ))
        ))
    );
    let (remainder, (intro, body)) = combinator(s)?;
    Ok((
        remainder,
        ASTNode::Clause(Box::new(Clause {
            intro,
            body
        }))
    ))
}

pub fn l2_clauses<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> { 
    context(
        "multiple l2 clauses",
        map(
            pair(
                l2_clause, 
                many0(pair(operator, alt((l2_clause, l2_relations))))
            ),
            join_nodes
        )
    )(s)
}

fn l1_clause<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "l1 clause",
        tuple((
            preceded(l1_bullet, alt((for_each, there_is))),
            alt((
                l2_relations,
                l2_clauses,
            )),
        ))
    );
    let (remainder, (intro, body)) = combinator(s)?;
    Ok((
        remainder,
        ASTNode::Clause(Box::new(Clause {
            intro,
            body
        }))
    ))
}

pub fn l1_clauses<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> { 
    context(
        "multiple l1 clauses",
        map(
            pair(
                alt((l1_clause, map(only_via_relation, |rel| ASTNode::Relation(rel)))),
                many0(tuple((operator, alt((l1_clause, map(only_via_relation, |rel| ASTNode::Relation(rel)))))))
            ),
            join_nodes
        )
    )(s)
}

fn conditional<'a>(s: &'a str) -> Res<&str, ClauseIntro<'a>> {
    let mut combinator = context(
        "conditional",
        delimited(tag("If"), relation, tuple((tag("then"), colon)))
    );
    let (remainder, relation) = combinator(s)?;
    Ok((remainder, ClauseIntro::Conditional(relation)))
}

fn for_each<'a>(s: &'a str) ->  Res<&str, ClauseIntro<'a>> {
    let mut combinator = context(
        "for each",
        delimited(
            tuple((tag("For each"), space1)),
            variable_intro,
            colon
        )
    );
    let (remainder, var_intro) = combinator(s)?;
    Ok((remainder, ClauseIntro::ForEach(var_intro)))
}

fn there_is<'a>(s: &'a str) ->  Res<&str, ClauseIntro<'a>> {
    let mut combinator = context(
        "there is",
        delimited(
            tag("There is a"), 
            variable_intro,
            tag("where:")
        )
    );
    let (remainder, var_intro) = combinator(s)?;
    Ok((remainder, ClauseIntro::ThereIs(var_intro)))
}
