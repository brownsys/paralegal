use super::{
    clause::l2_clauses, relations::l2_relations, shared::*, variable_intro::variable_intro, Res,
};
use crate::common::ast::*;
use nom::{
    branch::alt,
    character::complete::{multispace0, space1},
    combinator::opt,
    multi::many1,
    sequence::{delimited, preceded, tuple},
};

use nom_supreme::tag::complete::tag;

fn definition_scope(s: &str) -> Res<&str, DefinitionScope> {
    let mut combinator = opt(tag(", anywhere in the application"));

    let (remainder, res) = combinator(s)?;
    let scope = match res {
        None => DefinitionScope::Ctrler,
        Some(_) => DefinitionScope::Everywhere,
    };

    Ok((remainder, scope))
}

fn definition(s: &str) -> Res<&str, Definition> {
    let mut combinator = tuple((
        preceded(l1_bullet, variable),
        delimited(
            tuple((tag("is each"), space1)),
            variable_intro,
            tag("where"),
        ),
        definition_scope,
        preceded(colon, alt((l2_relations, l2_clauses))),
    ));

    let (remainder, (variable, declaration, scope, filter)) = combinator(s)?;

    Ok((
        remainder,
        Definition {
            variable,
            scope,
            declaration,
            filter: Some(filter),
            lifted_from: None,
        },
    ))
}

pub fn parse_definitions(s: &str) -> Res<&str, Vec<Definition>> {
    let (s, def) = opt(tuple((tag("Definitions"), colon)))(s)?;
    if def.is_none() {
        return Ok((s, vec![]));
    }
    many1(definition)(s)
}
