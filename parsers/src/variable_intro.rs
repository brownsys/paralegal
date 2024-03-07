use nom::{
    branch::alt,
    bytes::complete::tag,
    error::context,
    sequence::{separated_pair, delimited}, character::complete::space0,
};

use crate::{
    VariableIntro, Res, common::*,
};

pub fn variable_def<'a>(s: &'a str) -> Res<&str, VariableIntro<'a>> {
    let mut combinator = context(
        "variable (introduction)",
        variable
    );
    let (remainder, variable) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro::Variable(variable)
    ))
}

pub fn variable_marked<'a>(s: &'a str) -> Res<&str, VariableIntro<'a>> {
    let mut combinator = context(
        "variable marked",
        separated_pair(variable, tag("marked"), marker)
    );
    let (remainder, (variable, marker)) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro::VariableMarked((variable, marker))
    ))
} 

fn variable_type_marked<'a>(s: &'a str) -> Res<&str, VariableIntro<'a>> {
    let mut combinator = context(
        "variable type marked",
        separated_pair(variable, tag("type marked"), marker),
    );
    let (remainder, (variable, marker)) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro::VariableOfTypeMarked((variable, marker))
    ))
}

fn variable_source_of<'a>(s: &'a str) -> Res<&str, VariableIntro<'a>> {
    let mut combinator = context(
        "variable source of",
        separated_pair(variable, tag("that is a source of"), variable)
    );
    let (remainder, (source_of_var, var)) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro::VariableSourceof((source_of_var, var))
    ))
}

fn roots<'a>(s: &'a str) -> Res<&str, VariableIntro<'a>> {
    let mut combinator = context(
        "roots",
        tag("input")
    );
    let (remainder, _) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro::Roots
    ))
}

pub fn variable_intro<'a>(s: &'a str) -> Res<&str, VariableIntro<'a>> {
    context(
        "variable intro",
        delimited(
            space0, 
            alt((
                roots,
                variable_type_marked,
                variable_source_of,
                variable_marked,
                // must try this last b/c it'll partially consume the above
                variable_def,
            )), 
            space0)
    )(s)
}