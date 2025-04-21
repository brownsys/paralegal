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
    Negation,
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
            Template::Base => "misc/base.handlebars",
            Template::Main => "misc/main.handlebars",
            Template::Definition => "misc/definition.handlebars",
            Template::Roots => "variable-intros/roots.handlebars",
            Template::AllNodes => "variable-intros/all-nodes.handlebars",
            Template::Variable => "variable-intros/variable.handlebars",
            Template::VariableMarked => "variable-intros/variable-marked.handlebars",
            Template::VariableOfTypeMarked => "variable-intros/variable-of-type-marked.handlebars",
            Template::VariableSourceOf => "variable-intros/variable-source-of.handlebars",
            Template::OnlyViaIntro => "misc/only-via-intro.handlebars",
            Template::FlowsTo => "relations/flows-to.handlebars",
            Template::NoFlowsTo => "relations/no-flows-to.handlebars",
            Template::ControlFlow => "relations/control-flow.handlebars",
            Template::NoControlFlow => "relations/no-control-flow.handlebars",
            Template::OnlyVia => "misc/only-via.handlebars",
            Template::AssociatedCallSite => "relations/associated-call-site.handlebars",
            Template::IsMarked => "relations/is-marked.handlebars",
            Template::IsNotMarked => "relations/is-not-marked.handlebars",
            Template::Influences => "relations/influences.handlebars",
            Template::DoesNotInfluence => "relations/no-influences.handlebars",
            Template::ForEach => "clause-intros/for-each.handlebars",
            Template::ThereIs => "clause-intros/there-is.handlebars",
            Template::Conditional => "clause-intros/conditional.handlebars",
            Template::And => "misc/and.handlebars",
            Template::Or => "misc/or.handlebars",
            Template::Everywhere => "scope/everywhere.handlebars",
            Template::Somewhere => "scope/somewhere.handlebars",
            Template::InCtrler => "scope/in-ctrler.handlebars",
            Template::Negation => "relations/negation.handlebars",
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
        .unwrap_or_else(|_| panic!("Could not render {name} handlebars template"))
}

pub fn render_only_via_template(
    handlebars: &mut Handlebars,
    map: &HashMap<&str, Vec<String>>,
) -> String {
    let name: &str = Template::OnlyVia.into();
    handlebars
        .render(name, &map)
        .unwrap_or_else(|_| panic!("Could not render {name} handlebars template"))
}
