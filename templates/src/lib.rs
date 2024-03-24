use std::collections::HashMap;
use handlebars::{no_escape, Handlebars};
use strum::IntoEnumIterator;
use strum_macros::EnumIter;

#[derive(Debug, EnumIter)]
pub enum Template {
    // all policies use base; has infrastructure to set up and run policy
    Base,
    // variable intro
    Roots,
    Variable, // TODO not sure this needs one? but may be easier to just give it one bc everything else has one
    VariableMarked,
    VariableOfTypeMarked,
    VariableSourceOf,
    // relations
    FlowsTo,
    NoFlowsTo,
    ControlFlow,
    NoControlFlow,
    OnlyVia,
    AssociatedCallSite,
    IsMarked,
    IsNotMarked,
    Influences,
    DoesNotInfluence,
    // clause intro
    ForEach,
    ThereIs,
    Conditional,
    // operator
    And,
    Or,
    // scope
    Always,
    Sometimes,
    InCtrler,
}

impl From<Template> for &str {
    fn from(value: Template) -> Self {
        match value {
            Template::Base => "base",
            Template::Roots => "roots",
            Template::Variable => "variable",
            Template::VariableMarked => "variable-marked",
            Template::VariableOfTypeMarked => "variable-of-type-marked",
            Template::VariableSourceOf =>  "variable-source-of",
            Template::FlowsTo => "flows-to",
            Template::NoFlowsTo => "no-flows-to",
            Template::ControlFlow => "control-flow",
            Template::NoControlFlow => "no-control-flow",
            Template::OnlyVia => "only-via",
            Template::AssociatedCallSite => "associated-call-site",
            Template::IsMarked => "is-marked",
            Template::IsNotMarked => "is-not-marked",
            Template::Influences => "influences",
            Template::DoesNotInfluence => "does-not-influence",
            Template::ForEach => "for-each",
            Template::ThereIs => "there-is",
            Template::Conditional => "conditional",
            Template::And => "and",
            Template::Or => "or",
            Template::Always => "always",
            Template::Sometimes => "sometimes",
            Template::InCtrler => "in-ctrler",
        }
    }
}

pub fn register_templates(handlebars: &mut Handlebars) {
    handlebars.register_escape_fn(no_escape);
    for template in Template::iter() {
        let name : &str = template.into();
        let path : &str = &format!("templates/{name}.handlebars");
        handlebars
        .register_template_file(name, path)
        .expect(&format!(
            "Could not register {name} template with handlebars"
        ));
    }
}

pub fn render_template<'a>(
    handlebars: &mut Handlebars,
    map: &HashMap<&str, &str>,
    template: Template,
) -> String { 
    let name : &str = template.into();
    handlebars
        .render(name, &map)
        .expect(&format!("Could not render {name} handlebars template"))
}

/*

for variable marked, template to get all nodes marked marker and name it var
for variable of type marked, template to get all types marked marker and name it var
for variable source of, template to get all sources of type_var and name it var

*/
