use nom::{
    bytes::complete::tag,
    character::complete::{space1, multispace0},
    error::context,
    multi::many1,
    sequence::{preceded, tuple}, branch::alt,
};

use crate::{
    Definition, Res, common::*, 
    variable_intro::variable_intro, clause::l2_clauses, relations::l2_relations,
};

fn definition<'a>(s: &'a str) -> Res<&str, Definition<'a>> {
    let mut combinator = context(
        "definition",
        tuple((
            preceded(l1_bullet, variable),
            preceded(tuple((tag("is each"), space1)), variable_intro),
            preceded(tuple((tag("where"), colon)), alt((l2_relations, l2_clauses)))
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

pub fn parse_definitions<'a>(s: &'a str) -> Res<&str, Vec<Definition<'a>>> {
    context(
        "definitions",
        preceded(
            tuple((multispace0, tag("Definitions"), colon)),
            many1(definition)
        )
    )(s)
}