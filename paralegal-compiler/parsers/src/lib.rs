use clause::l1_clauses;
use common::*;
use definitions::parse_definitions;
use nom::{
    bytes::complete::tag,
    character::complete::multispace0,
    combinator::opt,
    sequence::{delimited, tuple},
    IResult,
};
use nom_supreme::{
    error::ErrorTree,
    final_parser::{final_parser, Location},
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
        opt(parse_definitions),
        delimited(
            tuple((multispace0, tag("Policy"), colon)),
            l1_clauses,
            multispace0,
        ),
    )));

    let (scope, option_defs, body) = combinator(s)?;
    let policy = Policy {
        definitions: option_defs.unwrap_or_default(),
        scope,
        body,
    };
    Ok(policy)
}
