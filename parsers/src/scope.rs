use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::multispace0,
    error::context,
    sequence::{preceded, tuple},
};

use crate::{common::*, PolicyScope, Res};

fn everywhere(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context("everywhere", preceded(multispace0, tag("Everywhere")));
    let (remainder, _) = combinator(s)?;
    Ok((remainder, PolicyScope::Everywhere))
}

fn somewhere(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context("somewhere", preceded(multispace0, tag("Somewhere")));
    let (remainder, _) = combinator(s)?;
    Ok((remainder, PolicyScope::Somewhere))
}

fn in_ctrler(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context(
        "in ctrler",
        preceded(tuple((multispace0, tag("In"))), alphabetic_with_underscores),
    );
    let (remainder, ctrler) = combinator(s)?;
    Ok((remainder, PolicyScope::InCtrler(ctrler)))
}

pub fn scope(s: &str) -> Res<&str, PolicyScope> {
    context(
        "scope",
        preceded(
            tuple((multispace0, tag("Scope"), colon)),
            alt((everywhere, somewhere, in_ctrler)),
        ),
    )(s)
}
