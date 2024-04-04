use nom::{
    branch::alt,
    bytes::complete::tag,
    error::context,
    sequence::{separated_pair, delimited, terminated}, character::complete::space0,
};

use crate::{
    VariableIntro, Res, common::*,
};

pub fn variable_def(s: &str) -> Res<&str, VariableIntro> {
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

pub fn variable_marked(s: &str) -> Res<&str, VariableIntro> {
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

fn variable_type_marked(s: &str) -> Res<&str, VariableIntro> {
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

fn variable_source_of(s: &str) -> Res<&str, VariableIntro> {
    let mut combinator = context(
        "variable source of",
        separated_pair(variable, tag("that is a source of"), variable)
    );
    let (remainder, (source_of_var, var)) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro::VariableSourceOf((source_of_var, var))
    ))
}

fn roots(s: &str) -> Res<&str, VariableIntro> {
    let mut combinator = context(
        "roots",
        terminated(variable, tag("input"))
    );
    let (remainder, var) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro::Roots(var)
    ))
}

fn nodes(s: &str) -> Res<&str, VariableIntro> {
    let mut combinator = context(
        "nodes",
        terminated(variable, tag("item"))
    );
    let (remainder, var) = combinator(s)?;
    Ok((
        remainder,
        VariableIntro::AllNodes(var)
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
            space0)
    )(s)
}