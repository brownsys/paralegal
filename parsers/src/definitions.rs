use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{multispace0, space1},
    combinator::opt,
    error::context,
    multi::many1,
    sequence::{delimited, preceded, tuple},
};

use crate::{
    clause::l2_clauses, common::*, relations::l2_relations, variable_intro::variable_intro,
    Definition, DefinitionScope, Res,
};

fn definition_scope(s: &str) -> Res<&str, DefinitionScope> {
    let mut combinator = context(
        "definition scope",
        opt(tag(", anywhere in the application")),
    );

    let (remainder, res) = combinator(s)?;
    let scope = match res {
        None => DefinitionScope::Ctrler,
        Some(_) => DefinitionScope::Everywhere,
    };

    Ok((remainder, scope))
}

fn definition(s: &str) -> Res<&str, Definition> {
    let mut combinator = context(
        "definition",
        tuple((
            preceded(l1_bullet, variable),
            delimited(
                tuple((tag("is each"), space1)),
                variable_intro,
                tag("where"),
            ),
            definition_scope,
            preceded(colon, alt((l2_relations, l2_clauses))),
        )),
    );

    let (remainder, (variable, declaration, scope, filter)) = combinator(s)?;

    Ok((
        remainder,
        Definition {
            variable,
            scope,
            declaration,
            filter,
        },
    ))
}

pub fn parse_definitions(s: &str) -> Res<&str, Vec<Definition>> {
    context(
        "definitions",
        preceded(
            tuple((multispace0, tag("Definitions"), colon)),
            many1(definition),
        ),
    )(s)
}
