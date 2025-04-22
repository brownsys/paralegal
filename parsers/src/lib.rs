use clause::l1_clauses;
use common::*;
use definitions::parse_definitions;
use nom::{
    bytes::complete::tag,
    character::complete::multispace0,
    combinator::{all_consuming, opt},
    error::{context, VerboseError},
    sequence::{delimited, tuple},
    IResult,
};
use optimizer::optimize;
use scope::scope;
use shared::colon;

pub mod clause;
pub mod definitions;
pub mod relations;
pub mod scope;
pub mod shared;
pub mod variable_intro;

pub type Res<T, U> = IResult<T, U, VerboseError<T>>;

pub fn parse(s: &str) -> Res<&str, Policy> {
    let mut combinator = context(
        "parse policy",
        all_consuming(tuple((
            scope,
            opt(parse_definitions),
            delimited(
                tuple((multispace0, tag("Policy"), colon)),
                l1_clauses,
                multispace0,
            ),
        ))),
    );

    let (remainder, (scope, option_defs, body)) = combinator(s)?;
    let mut policy = Policy {
        definitions: option_defs.unwrap_or_default(),
        scope,
        body,
    };
    optimize(&mut policy);
    Ok((remainder, policy))
}
