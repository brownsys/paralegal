use nom::{
    branch::alt,
    bytes::complete::tag,
    error::context,
    sequence::{terminated, tuple, delimited, preceded}, character::complete::space1,
};

use crate::{
    ASTNode, Operator, TwoNodeObligation, Res, common::*, relations::*,
    variable_intro::variable_intro, VariableIntro, Quantifier, VariableClause,
};

fn conditional<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "conditional",
        tuple((
            delimited(tuple((bullet, tag("if"))), relation, tuple((tag("then"), colon))),
            variable_clause_body
        ))
    );
    let (remainder, (src, dest)) = combinator(s)?;
    Ok((remainder, 
        ASTNode::Conditional(
            Box::new(TwoNodeObligation { src, dest })
        )
    ))
}

pub fn body<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    context(
        "body",
        alt((
            multiple_bodies,
            conditional,
            preceded(bullet, relation)
        ))
    )(s)
}

fn multiple_bodies<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "multiple bodies",
        preceded(
            bullet,
            tuple((
                relation,
                operator, 
                body
            ))
        )
    );
    let (remainder, (src, operator, dest)) = combinator(s)?;
    let body = Box::new(TwoNodeObligation {src, dest});

    let node = match operator {
        Operator::And => ASTNode::And(body),
        Operator::Or => ASTNode::Or(body),
    };

    Ok((remainder, node))
}

fn variable_clause_body<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    context(
        "variable clause body",
        alt((
            inner_multiple_variable_clauses,
            variable_clause,
            body
        ))
    )(s)
}

fn inner_multiple_variable_clauses<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "multiple clauses",
        tuple((
            alt((variable_clause, body)),
            operator,
            variable_clause_body,
        )),
    );
    let (remainder, (src, operator, dest)) = combinator(s)?;
    let body = Box::new(TwoNodeObligation {src, dest});

    let node = match operator {
        Operator::And => ASTNode::And(body),
        Operator::Or => ASTNode::Or(body),
    };

    Ok((remainder, node))
}

fn for_each<'a>(s: &'a str) ->  Res<&str, (Quantifier, VariableIntro<'a>)> {
    let mut combinator = context(
        "for each",
        delimited(
            tuple((tag("for each"), space1)),
            variable_intro,
            colon
        )
    );
    let (remainder, var_intro) = combinator(s)?;
    Ok((remainder, (Quantifier::All, var_intro)))
}

fn there_is<'a>(s: &'a str) ->  Res<&str, (Quantifier, VariableIntro<'a>)> {
    let mut combinator = context(
        "there is",
        preceded(
            tag("there is a"), 
            variable_intro
        )
    );
    let (remainder, var_intro) = combinator(s)?;
    Ok((remainder, (Quantifier::Some, var_intro)))
}

fn clause_intro<'a>(s: &'a str) ->  Res<&str, (Quantifier, VariableIntro<'a>)> {
    context(
        "clause intro",
        preceded(
            bullet,
            alt((
                for_each,
                terminated(there_is, tag("where:"))
            ))
        )
    )(s)
}

pub fn variable_clause<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "variable clause", 
        tuple((
            clause_intro, 
            variable_clause_body
        ))
    );
    let (remainder, ((quantifier, intro), body)) = combinator(s)?;
    Ok((
        remainder,
        ASTNode::VarClause(
            Box::new(VariableClause {quantifier, intro, body})
        )
    ))

}