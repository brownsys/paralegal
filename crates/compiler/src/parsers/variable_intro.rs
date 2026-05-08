use nom::{
    branch::alt,
    character::complete::space0,
    combinator::peek,
    error::context,
    sequence::{delimited, separated_pair, terminated, tuple},
};
use nom_supreme::tag::complete::tag;

use super::{
    shared::{marker, variable},
    Res,
};
use crate::common::ast::*;

pub fn variable_def(s: &str) -> Res<&str, VariableIntro> {
    let (remainder, variable) = variable(s)?;
    Ok((
        remainder,
        VariableIntro {
            variable,
            intro: VariableIntroType::Variable,
        },
    ))
}

pub fn variable_marked(s: &str) -> Res<&str, VariableIntro> {
    let mut combinator = separated_pair(variable, tag("marked"), marker);
    let (remainder, (variable, marker)) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro {
            variable,
            intro: VariableIntroType::VariableMarked {
                marker,
                on_type: false,
            },
        },
    ))
}

fn variable_type_marked(s: &str) -> Res<&str, VariableIntro> {
    let mut combinator = separated_pair(variable, tag("type marked"), marker);
    let (remainder, (variable, marker)) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro {
            variable,
            intro: VariableIntroType::VariableMarked {
                marker,
                on_type: true,
            },
        },
    ))
}

fn variable_source_of(s: &str) -> Res<&str, VariableIntro> {
    let mut combinator = separated_pair(variable, tag("that produces"), variable);
    let (remainder, (source_of_var, var)) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro {
            variable: source_of_var,
            intro: VariableIntroType::VariableSourceOf(var),
        },
    ))
}

fn roots(s: &str) -> Res<&str, VariableIntro> {
    let mut combinator = terminated(variable, tag("input"));
    let (remainder, var) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro {
            variable: var,
            intro: VariableIntroType::Roots,
        },
    ))
}

fn nodes(s: &str) -> Res<&str, VariableIntro> {
    let mut combinator = terminated(variable, tag("item"));
    let (remainder, var) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro {
            variable: var,
            intro: VariableIntroType::AllNodes,
        },
    ))
}

pub fn variable_intro(s: &str) -> Res<&str, VariableIntro> {
    let (remainder, _) = context(
        "a variable introduction, e.g. \"sensitive\"",
        tuple((space0, peek(variable))),
    )(s)?;
    delimited(
        space0,
        alt((
            roots,
            nodes,
            variable_type_marked,
            variable_source_of,
            variable_marked,
            // must try this last b/c it'll partially consume the above
            variable_def,
        )),
        space0,
    )(remainder)
}
