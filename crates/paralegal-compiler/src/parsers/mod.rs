use crate::common::*;
use clause::l1_clauses;
use definitions::parse_definitions;
use nom::{
    character::complete::multispace0,
    sequence::{delimited, tuple},
    IResult,
};
use nom_supreme::{
    error::ErrorTree,
    final_parser::{final_parser, Location},
    tag::complete::tag,
};
use scope::scope;
use shared::colon;

pub mod clause;
pub mod definitions;
pub mod relations;
pub mod scope;
pub mod shared;
pub mod variable_intro;

pub type Res<T, U> = IResult<T, U, ErrorTree<T>>;

pub fn parse(s: &str) -> Result<Policy, ErrorTree<Location>> {
    let mut combinator = final_parser(tuple((
        scope,
        multispace0,
        parse_definitions,
        delimited(
            tuple((multispace0, tag("Policy"), colon)),
            l1_clauses,
            multispace0,
        ),
    )));

    let (scope, _, option_defs, body) = combinator(s)?;
    let policy = Policy {
        definitions: option_defs,
        scope,
        body,
    };
    Ok(policy)
}
