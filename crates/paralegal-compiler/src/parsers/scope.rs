use nom::{
    branch::alt,
    character::complete::multispace0,
    sequence::{preceded, tuple},
};
use nom_supreme::tag::complete::tag;

use super::{shared::*, Res};
use crate::common::*;

fn everywhere(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = preceded(multispace0, tag("Everywhere"));
    let (remainder, _) = combinator(s)?;
    Ok((remainder, PolicyScope::Everywhere))
}

fn somewhere(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = preceded(multispace0, tag("Somewhere"));
    let (remainder, _) = combinator(s)?;
    Ok((remainder, PolicyScope::Somewhere))
}

fn in_ctrler(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = preceded(tuple((multispace0, tag("In"))), alphabetic_with_underscores);
    let (remainder, ctrler) = combinator(s)?;
    Ok((remainder, PolicyScope::InCtrler(ctrler)))
}

pub fn scope(s: &str) -> Res<&str, PolicyScope> {
    preceded(
        tuple((multispace0, tag("Scope"), colon)),
        alt((everywhere, somewhere, in_ctrler)),
    )(s)
}
