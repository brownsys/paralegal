use nom::{
    branch::alt,
    error::context,
    sequence::{tuple, delimited}, character::complete::multispace0, bytes::complete::tag,
};

use crate::{
    PolicyScope, Res, common::*,
};


fn always(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context(
        "always",
        tuple((multispace0, tag("Always"), colon)),
    );
    let (remainder, _) = combinator(s)?;
    Ok((remainder, PolicyScope::Always))
}

fn sometimes(s: &str) -> Res<&str, PolicyScope> {
    let mut combinator = context(
        "sometimes",
        tuple((multispace0, tag("Sometimes"), colon)),
    );
    let (remainder, _) = combinator(s)?;
    Ok((remainder, PolicyScope::Sometimes))
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
        alt((always, sometimes, in_ctrler))
    )(s)
}