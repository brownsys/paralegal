use nom::{
    branch::alt,
    error::context,
    sequence::{tuple, preceded}, character::complete::multispace0, bytes::complete::tag,
};

use crate::{
    PolicyScope, Res, common::*,
};


fn everywhere(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context(
        "everywhere",
        preceded(multispace0, tag("Everywhere")),
    );
    let (remainder, _) = combinator(s)?;
    Ok((remainder, PolicyScope::Everywhere))
}

fn somewhere(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context(
        "somewhere",
        preceded(multispace0, tag("Somewhere")),
    );
    let (remainder, _) = combinator(s)?;
    Ok((remainder, PolicyScope::Somewhere))
}

fn in_ctrler(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context(
        "in ctrler",
        preceded(
            tuple((multispace0, tag("In"))),
            alphabetic_with_underscores, 
        )
    );
    let (remainder, ctrler) = combinator(s)?;
    Ok((remainder, PolicyScope::InCtrler(ctrler)))
}

pub fn scope(s: &str) -> Res<&str, PolicyScope> {
    context("scope", 
        preceded(
            tuple((multispace0, tag("Scope"), colon)), 
            alt((everywhere, somewhere, in_ctrler))
        )
    )(s)
}