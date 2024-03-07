use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, space0, space1, multispace0, multispace1},
    combinator::{opt, recognize},
    error::context,
    multi::many1,
    sequence::{delimited, terminated, tuple, preceded, separated_pair},
};

use crate::{
    Marker, Operator, Variable, Res, VariableIntro
};

pub fn colon(s: &str) -> Res<&str, &str> {
    context("colon", delimited(space0, tag(":"), multispace0))(s)
}

pub fn and(s: &str) -> Res<&str, &str> {
    context("and", delimited(multispace0, tag("and"), multispace1))(s)
}

pub fn or(s: &str) -> Res<&str, &str> {
    context("or", delimited(multispace0, tag("or"), multispace1))(s)
}

pub fn operator<'a>(s: &'a str) -> Res<&str, Operator> {
    let mut combinator = context("operator", alt((and, or)));
    let (remainder, operator_str) = combinator(s)?;
    Ok((remainder, operator_str.into()))
}

pub fn bullet(s: &str) -> Res<&str, &str> {
    context("bullet", 
        delimited(
            multispace0,
            alphanumeric1, 
            tuple((tag("."), space1))
        )
    )(s)
}

pub fn alphabetic_with_underscores<'a>(s: &'a str) -> Res<&str, Marker<'a>> {
    context(
        "alphabetic with underscores",
        preceded(
            space0,
            recognize(
                many1(
                    tuple((alpha1, opt(tag("_"))))
                )
            ),
        )
    )(s)
}

pub fn marker<'a>(s: &'a str) -> Res<&str, Marker<'a>> {
    context(
        "marker",
        terminated(
            alphabetic_with_underscores,
            multispace0
        )
    )(s)
}

pub fn variable<'a>(s: &'a str) -> Res<&str, Variable<'a>> {
    context(
        "variable",
        alt((
            delimited(
                tuple((space0, tag("\""))),
                alphabetic_with_underscores,
                tuple((tag("\""), space0)), 
            ),
            delimited(
                tuple((space0, tag("\""))),
                recognize(
                        many1(tuple((alpha1, opt(space1))))
                    ),
                tuple((tag("\""), space0)), 
            )
        ))
        
    )(s)
}
