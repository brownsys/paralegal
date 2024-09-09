use handlebars::{no_escape, Handlebars};
use std::collections::HashMap;
use strum_macros::EnumIter;

#[derive(Debug, EnumIter)]
pub enum Template {
    // all policies use base
    Base,
    // If we are creating a runnable binary we use this, which also includes base
    Main,
    Definition,
    // variable intro
    Roots,
    AllNodes,
    Variable, // TODO not sure this needs one? but may be easier to just give it one bc everything else has one
    VariableMarked,
    VariableOfTypeMarked,
    VariableSourceOf,
    OnlyViaIntro,
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
    Everywhere,
    Somewhere,
    InCtrler,
}

#[derive(rust_embed::RustEmbed)]
#[folder = "handlebars"]
struct TemplateDirectory;

impl From<Template> for &str {
    fn from(value: Template) -> Self {
        match value {
            Template::Base => "misc/base",
            Template::Main => "misc/main",
            Template::Definition => "misc/definition",
            Template::Roots => "variable-intros/roots",
            Template::AllNodes => "variable-intros/all-nodes",
            Template::Variable => "variable-intros/variable",
            Template::VariableMarked => "variable-intros/variable-marked",
            Template::VariableOfTypeMarked => "variable-intros/variable-of-type-marked",
            Template::VariableSourceOf => "variable-intros/variable-source-of",
            Template::OnlyViaIntro => "misc/only-via-intro",
            Template::FlowsTo => "relations/flows-to",
            Template::NoFlowsTo => "relations/no-flows-to",
            Template::ControlFlow => "relations/control-flow",
            Template::NoControlFlow => "relations/no-control-flow",
            Template::OnlyVia => "misc/only-via",
            Template::AssociatedCallSite => "relations/associated-call-site",
            Template::IsMarked => "relations/is-marked",
            Template::IsNotMarked => "relations/is-not-marked",
            Template::Influences => "relations/influences",
            Template::DoesNotInfluence => "relations/no-influences",
            Template::ForEach => "clause-intros/for-each",
            Template::ThereIs => "clause-intros/there-is",
            Template::Conditional => "clause-intros/conditional",
            Template::And => "misc/and",
            Template::Or => "misc/or",
            Template::Everywhere => "scope/everywhere",
            Template::Somewhere => "scope/somewhere",
            Template::InCtrler => "scope/in-ctrler",
        }
    }
}

pub fn register_templates(handlebars: &mut Handlebars) {
    handlebars.register_escape_fn(no_escape);
    handlebars
        .register_embed_templates::<TemplateDirectory>()
        .unwrap();
}

pub fn render_template(
    handlebars: &mut Handlebars,
    map: &HashMap<&str, String>,
    template: Template,
) -> String {
    let name: &str = template.into();
    handlebars
        .render(name, &map)
        .expect(&format!("Could not render {name} handlebars template"))
}

pub fn render_only_via_template(
    handlebars: &mut Handlebars,
    map: &HashMap<&str, Vec<String>>,
) -> String {
    let name: &str = Template::OnlyVia.into();
    handlebars
        .render(name, &map)
        .expect(&format!("Could not render {name} handlebars template"))
}

/*

for variable marked, template to get all nodes marked marker and name it var
for variable of type marked, template to get all types marked marker and name it var
for variable source of, template to get all sources of type_var and name it var

*/
