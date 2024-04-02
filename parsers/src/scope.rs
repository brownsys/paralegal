use nom::{
    branch::alt,
    error::context,
    sequence::{tuple, delimited}, character::complete::multispace0, bytes::complete::tag,
};

use crate::{
    PolicyScope, Res, common::*,
};


fn everywhere(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context(
        "everywhere",
        tuple((multispace0, tag("Everywhere"), colon)),
    );
    let (remainder, _) = combinator(s)?;
    Ok((remainder, PolicyScope::Everywhere))
}

fn somewhere(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context(
        "somewhere",
        tuple((multispace0, tag("Somewhere"), colon)),
    );
    let (remainder, _) = combinator(s)?;
    Ok((remainder, PolicyScope::Somewhere))
}

fn in_ctrler(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context(
        "in ctrler",
        delimited(
            tuple((multispace0, tag("In"))),
            alphabetic_with_underscores, 
            colon,
        )
    );
    let (remainder, ctrler) = combinator(s)?;
    Ok((remainder, PolicyScope::InCtrler(ctrler)))
}

pub fn scope(s: &str) -> Res<&str, PolicyScope> {
    context("scope", 
        alt((everywhere, somewhere, in_ctrler))
    )(s)
}