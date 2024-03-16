use nom::{
    branch::alt,
    bytes::complete::tag,
    error::context,
    sequence::{terminated, tuple, delimited, preceded, pair}, character::complete::space1, multi::many0, combinator::map,
};

use crate::{
    ASTNode, Res, common::*, relations::*,
    variable_intro::variable_intro, VariableIntro, ClauseType, VariableClause, conditional::{l2_conditional, l3_conditional, l4_conditional},
};

fn l4_clause<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "l4 clause",
        tuple((
            preceded(l4_bullet, clause_intro),
            l5_relations,
        ))
    );
    let (remainder, ((typ, intro), body)) = combinator(s)?;
    Ok((
        remainder,
        ASTNode::VarClause(Box::new(VariableClause {
            typ,
            intro,
            body
        }))
    ))
}

pub fn l4_clauses<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> { 
    context(
        "multiple l4 clauses",
        map(
            pair(l4_clause, 
                alt((
                    many0(tuple((operator, l4_clause))),
                    many0(tuple((operator, preceded(l4_bullet, relation))))
                ))
            ),
            join_nodes
        )
    )(s)
}

fn l3_clause<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "l3 clause",
        tuple((
            preceded(l3_bullet, clause_intro),
            alt((
                l4_relations,
                l4_clauses
            ))
        ))
    );
    let (remainder, ((typ, intro), body)) = combinator(s)?;
    Ok((
        remainder,
        ASTNode::VarClause(Box::new(VariableClause {
            typ,
            intro,
            body
        }))
    ))
}

pub fn l3_clauses<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> { 
    context(
        "multiple l3 clauses",
        map(
            pair(l3_clause, 
                alt((
                    many0(tuple((operator, l3_clause))),
                    many0(tuple((operator, preceded(l3_bullet, relation))))
                ))
            ),
            join_nodes
        )
    )(s)
}

fn l2_clause<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "l2 clause",
        tuple((
            preceded(l2_bullet, clause_intro),
            alt((
                l3_relations,
                l3_clauses,
            ))
        ))
    );
    let (remainder, ((typ, intro), body)) = combinator(s)?;
    Ok((
        remainder,
        ASTNode::VarClause(Box::new(VariableClause {
            typ,
            intro,
            body
        }))
    ))
}

pub fn l2_clauses<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> { 
    context(
        "multiple l2 clauses",
        map(
            pair(l2_clause, 
                alt((
                    many0(tuple((operator, l2_clause))),
                    many0(tuple((operator, preceded(l2_bullet, relation))))
                ))
            ),
            join_nodes
        )
    )(s)
}

fn l1_clause<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "l1 clause",
        tuple((
            preceded(l1_bullet, clause_intro),
            alt((
                l2_relations,
                l2_clauses,
            ))
        ))
    );
    let (remainder, ((typ, intro), body)) = combinator(s)?;
    Ok((
        remainder,
        ASTNode::VarClause(Box::new(VariableClause {
            typ,
            intro,
            body
        }))
    ))
}

pub fn l1_clauses<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> { 
    context(
        "multiple l1 clauses",
        map(
            pair(l1_clause, many0(tuple((operator, l1_clause)))),
            join_nodes
        )
    )(s)
}


fn for_each<'a>(s: &'a str) ->  Res<&str, (ClauseType, VariableIntro<'a>)> {
    let mut combinator = context(
        "for each",
        delimited(
            tuple((tag("For each"), space1)),
            variable_intro,
            colon
        )
    );
    let (remainder, var_intro) = combinator(s)?;
    Ok((remainder, (ClauseType::ForEach, var_intro)))
}

fn there_is<'a>(s: &'a str) ->  Res<&str, (ClauseType, VariableIntro<'a>)> {
    let mut combinator = context(
        "there is",
        preceded(
            tag("There is a"), 
            variable_intro
        )
    );
    let (remainder, var_intro) = combinator(s)?;
    Ok((remainder, (ClauseType::ThereIs, var_intro)))
}

pub fn clause_intro<'a>(s: &'a str) ->  Res<&str, (ClauseType, VariableIntro<'a>)> {
    context(
        "clause intro",
        alt((
            for_each,
            terminated(there_is, tag("where:"))
        ))
    )(s)
}
