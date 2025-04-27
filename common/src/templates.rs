use handlebars::{no_escape, Handlebars};
use std::collections::HashMap;
use strum_macros::EnumIter;

use crate::{
    ast::{ASTNode, Binop, ClauseIntro, Operator, Position, Relation, VariableIntro},
    PolicyScope,
};

#[derive(Clone, Debug, EnumIter, strum_macros::Display)]
pub enum Template {
    // all policies use base
    Base,
    // If we are creating a runnable binary we use this, which also includes base
    Main,
    GlobalDefinition,
    Definition,
    // variable intro
    Roots,
    AllNodes,
    Variable,
    VariableMarked,
    VariableOfTypeMarked,
    VariableSourceOf,
    OnlyViaIntro,
    // relations
    FlowsTo,
    ControlFlow,
    OnlyVia,
    AssociatedCallSite,
    IsMarked,
    Influences,
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
    // Fused clause templates
    BothSource,
    BothTarget,
    ControlSource,
    ControlTarget,
    DataSource,
    DataTarget,
}

#[derive(rust_embed::RustEmbed)]
#[folder = "handlebars"]
struct TemplateDirectory;

impl From<Template> for &str {
    fn from(value: Template) -> Self {
        match value {
            Template::Base => "misc/base.handlebars",
            Template::Main => "misc/main.handlebars",
            Template::GlobalDefinition => "definitions/global-definition.handlebars",
            Template::Definition => "definitions/definition.handlebars",
            Template::Roots => "variable-intros/roots.handlebars",
            Template::AllNodes => "variable-intros/all-nodes.handlebars",
            Template::Variable => "variable-intros/variable.handlebars",
            Template::VariableMarked => "variable-intros/variable-marked.handlebars",
            Template::VariableOfTypeMarked => "variable-intros/variable-of-type-marked.handlebars",
            Template::VariableSourceOf => "variable-intros/variable-source-of.handlebars",
            Template::OnlyViaIntro => "misc/only-via-intro.handlebars",
            Template::FlowsTo => "relations/flows-to.handlebars",
            Template::ControlFlow => "relations/control-flow.handlebars",
            Template::OnlyVia => "misc/only-via.handlebars",
            Template::AssociatedCallSite => "relations/associated-call-site.handlebars",
            Template::IsMarked => "relations/is-marked.handlebars",
            Template::Influences => "relations/influences.handlebars",
            Template::ForEach => "clause-intros/for-each.handlebars",
            Template::ThereIs => "clause-intros/there-is.handlebars",
            Template::Conditional => "clause-intros/conditional.handlebars",
            Template::And => "misc/and.handlebars",
            Template::Or => "misc/or.handlebars",
            Template::Everywhere => "scope/everywhere.handlebars",
            Template::Somewhere => "scope/somewhere.handlebars",
            Template::InCtrler => "scope/in-ctrler.handlebars",
            Template::Negation => "relations/negation.handlebars",
            Template::BothSource => "fused-clauses/both-source.handlebars",
            Template::BothTarget => "fused-clauses/both-target.handlebars",
            Template::ControlSource => "fused-clauses/control-source.handlebars",
            Template::ControlTarget => "fused-clauses/control-target.handlebars",
            Template::DataSource => "fused-clauses/data-source.handlebars",
            Template::DataTarget => "fused-clauses/data-target.handlebars",
        }
    }
}

// map templates to their handlebars template file names
impl From<&VariableIntro> for Template {
    fn from(value: &VariableIntro) -> Self {
        use crate::ast::VariableIntroType::*;
        match value.intro {
            Roots => Template::Roots,
            AllNodes => Template::AllNodes,
            Variable => Template::Variable,
            VariableMarked { on_type, .. } => {
                if on_type {
                    Template::VariableOfTypeMarked
                } else {
                    Template::VariableMarked
                }
            }
            VariableSourceOf(_) => Template::VariableSourceOf,
        }
    }
}

impl From<&Relation> for Template {
    fn from(value: &Relation) -> Self {
        match &value {
            Relation::Binary { typ, .. } => match typ {
                Binop::AssociatedCallSite => Template::AssociatedCallSite,
                Binop::Data => Template::FlowsTo,
                Binop::Control => Template::ControlFlow,
                Binop::Both => Template::Influences,
            },
            Relation::IsMarked { .. } => Template::IsMarked,
            Relation::Negation(_) => Template::Negation,
        }
    }
}

impl From<&Operator> for Template {
    fn from(value: &Operator) -> Self {
        match *value {
            Operator::And => Template::And,
            Operator::Or => Template::Or,
        }
    }
}

impl From<PolicyScope> for Template {
    fn from(value: PolicyScope) -> Self {
        match value {
            PolicyScope::Everywhere => Template::Everywhere,
            PolicyScope::Somewhere => Template::Somewhere,
            PolicyScope::InCtrler(_) => Template::InCtrler,
        }
    }
}

impl From<&ClauseIntro> for Template {
    fn from(value: &ClauseIntro) -> Self {
        match *value {
            ClauseIntro::ForEach(_) => Template::ForEach,
            ClauseIntro::ThereIs(_) => Template::ThereIs,
            ClauseIntro::Conditional(_) => Template::Conditional,
        }
    }
}

impl From<&ASTNode> for Template {
    fn from(value: &ASTNode) -> Self {
        match value {
            ASTNode::Relation(relation) => relation.into(),
            ASTNode::OnlyVia { .. } => Template::OnlyVia,
            ASTNode::Clause(clause) => (&clause.intro).into(),
            ASTNode::JoinedNodes(obligation) => (&obligation.op).into(),
            ASTNode::FusedClause(clause) => match (&clause.binop, &clause.pos) {
                (Binop::AssociatedCallSite, _) => unreachable!("not eligible for fusing"),
                (Binop::Both, Position::Source) => Template::BothSource,
                (Binop::Both, Position::Target) => Template::BothTarget,
                (Binop::Control, Position::Source) => Template::ControlSource,
                (Binop::Control, Position::Target) => Template::ControlTarget,
                (Binop::Data, Position::Source) => Template::DataSource,
                (Binop::Data, Position::Target) => Template::DataTarget,
            },
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
    let name: &str = template.clone().into();
    if let Some(partial_content) = TemplateDirectory::get("fused-clauses/partial.handlebars") {
        let partial_str = std::str::from_utf8(partial_content.data.as_ref())
            .expect("Failed to convert partial template to UTF-8");
        handlebars
            .register_partial("fused-partial", partial_str)
            .unwrap();
    }

    handlebars
        .render(name, &map)
        .unwrap_or_else(|e| panic!("Could not render {name} handlebars template {template}: {e}"))
}

pub fn render_only_via_template(
    handlebars: &mut Handlebars,
    map: &HashMap<&str, Vec<String>>,
) -> String {
    let template = Template::OnlyVia;
    let name: &str = Template::OnlyVia.into();
    handlebars
        .render(name, &map)
        .unwrap_or_else(|e| panic!("Could not render {name} handlebars template {template}: {e}"))
}
