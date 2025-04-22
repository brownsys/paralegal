use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::space0,
    error::context,
    sequence::{delimited, separated_pair, terminated},
};

use crate::{
    shared::{marker, variable},
    Res,
};
use common::ast::*;

pub fn variable_def(s: &str) -> Res<&str, VariableIntro> {
    let mut combinator = context("variable (introduction)", variable);
    let (remainder, variable) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro {
            variable,
            intro: VariableIntroType::Variable,
        },
    ))
}

pub fn variable_marked(s: &str) -> Res<&str, VariableIntro> {
    let mut combinator = context(
        "variable marked",
        separated_pair(variable, tag("marked"), marker),
    );
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
    let mut combinator = context(
        "variable type marked",
        separated_pair(variable, tag("type marked"), marker),
    );
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
    let mut combinator = context(
        "variable source of",
        separated_pair(variable, tag("that produces"), variable),
    );
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
    let mut combinator = context("roots", terminated(variable, tag("input")));
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
    let mut combinator = context("nodes", terminated(variable, tag("item")));
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
    context(
        "variable intro",
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
        ),
    )(s)
}
