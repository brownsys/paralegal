use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{space1, multispace0},
    error::context,
    multi::many1,
    sequence::{preceded, tuple},
};

use crate::{
    Definition, Res, common::*, 
    variable_intro::variable_intro, policy_body::exprs, variable_clause::body,
};

fn definition<'a>(s: &'a str) -> Res<&str, Definition<'a>> {
    let mut combinator = context(
        "definition",
        tuple((
            preceded(bullet, variable),
            preceded(tuple((tag("is each"), space1)), variable_intro),
            preceded(tuple((tag("where"), colon)), alt((exprs, body)))
        ))
    );

    let (remainder, (variable, declaration, filter)) = combinator(s)?;
    
    Ok((
        remainder,
        Definition { 
            variable,
            declaration,
            filter
        }
    ))
}

fn multiple_definitions<'a>(s: &'a str) -> Res<&str, Vec<Definition<'a>>> {
    context(
        "multiple definitions",
        many1(definition)
    )(s)
}

pub fn parse_definitions<'a>(s: &'a str) -> Res<&str, Vec<Definition<'a>>> {
    context(
        "definitions",
        preceded(
            tuple((multispace0, tag("definitions"), colon)),
            multiple_definitions
        )
    )(s)
}