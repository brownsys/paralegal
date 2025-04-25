use common::{ast::*, Policy, PolicyScope};
use handlebars::Handlebars;
use std::fs;
use std::io::Result;
use std::process::Command;
use std::{collections::HashMap, path::Path};

use common::templates::*;
use common::verify_scope::*;

fn compile_variable_intro(
    handlebars: &mut Handlebars,
    intro: &VariableIntro,
    is_definition: bool,
) -> (String, String) {
    let mut map: HashMap<&str, String> = HashMap::new();
    map.insert("var", intro.variable.clone());

    match &intro.intro {
        VariableIntroType::Roots | VariableIntroType::AllNodes => (),
        VariableIntroType::Variable => {}
        VariableIntroType::VariableMarked { marker, .. } => {
            map.insert("marker", marker.into());
            if is_definition {
                map.insert("lifted", is_definition.to_string());
            }
        }
        VariableIntroType::VariableSourceOf(type_var) => {
            map.insert("type-var", type_var.into());
            if is_definition {
                map.insert("lifted", is_definition.to_string());
            }
        }
    };
    (
        intro.variable.clone(),
        render_template(handlebars, &map, intro.into()),
    )
}

fn compile_relation(handlebars: &mut Handlebars, relation: &Relation) -> String {
    let mut map: HashMap<&str, String> = HashMap::new();
    match relation {
        Relation::Binary { left, right, .. } => {
            map.insert("src", left.into());
            map.insert("sink", right.into());
        }
        Relation::Negation(inner) => {
            let value = compile_relation(handlebars, inner);
            map.insert("value", value);
        }
        Relation::IsMarked(var, marker) => {
            map.insert("src", var.into());
            map.insert("marker", marker.into());
        }
    }
    render_template(handlebars, &map, relation.into())
}

// for joined nodes, we don't know how many expressions we're and/oring together in the whole policy,
// so use the counter to give each variable a unique name -- see and/or templates for more context
fn compile_ast_node(handlebars: &mut Handlebars, node: &ASTNode, counter: &mut u32) -> String {
    let mut map: HashMap<&str, String> = HashMap::new();
    match node {
        ASTNode::Relation(relation) => compile_relation(handlebars, relation),
        ASTNode::OnlyVia(src_intro, sink_intro, checkpoint_intro) => {
            let mut only_via_map: HashMap<&str, Vec<String>> = HashMap::new();

            let (src_var, compiled_src_intro) =
                compile_variable_intro(handlebars, src_intro, false);
            map.insert("intro", compiled_src_intro);
            let src_intro = render_template(handlebars, &map, Template::OnlyViaIntro);
            map.remove_entry("var-definition");
            only_via_map.insert("src-intros", vec![src_intro]);
            only_via_map.insert("src", vec![src_var]);

            match &sink_intro.0 {
                // an operator is present, so there are multiple variable intros in the vector
                Some(op) => {
                    let mut compiled_intros: Vec<String> = vec![];
                    let mut vars: Vec<String> = vec![];
                    for intro in &sink_intro.1 {
                        let (sink_var, compiled_sink_intro) =
                            compile_variable_intro(handlebars, intro, false);
                        map.insert("intro", compiled_sink_intro);
                        let only_via_intro =
                            render_template(handlebars, &map, Template::OnlyViaIntro);
                        map.remove_entry("var-definition");
                        compiled_intros.push(only_via_intro);
                        vars.push(sink_var);
                    }
                    only_via_map.insert("sink-intros", compiled_intros);
                    only_via_map.insert("sink-names", vars);
                    if let &Operator::Or = op {
                        only_via_map.insert("sink-or", vec![String::from("true")]);
                    }
                }
                // no operator, so just a single variable intro in the vector
                None => {
                    let (sink_var, compiled_sink_intro) =
                        compile_variable_intro(handlebars, &sink_intro.1[0], false);
                    map.insert("intro", compiled_sink_intro);
                    let only_via_intro = render_template(handlebars, &map, Template::OnlyViaIntro);
                    map.remove_entry("var-definition");
                    only_via_map.insert("sink-intros", vec![only_via_intro]);
                    only_via_map.insert("sink-names", vec![sink_var]);
                }
            }

            match &checkpoint_intro.0 {
                // an operator is present, so there are multiple variable intros in the vector
                Some(op) => {
                    let mut compiled_intros: Vec<String> = vec![];
                    let mut vars: Vec<String> = vec![];
                    for intro in &checkpoint_intro.1 {
                        let (checkpoint_var, compiled_checkpoint_intro) =
                            compile_variable_intro(handlebars, intro, false);
                        map.insert("intro", compiled_checkpoint_intro);
                        let only_via_intro =
                            render_template(handlebars, &map, Template::OnlyViaIntro);
                        map.remove_entry("var-definition");
                        compiled_intros.push(only_via_intro);
                        vars.push(checkpoint_var);
                    }
                    only_via_map.insert("checkpoint-intros", compiled_intros);
                    only_via_map.insert("checkpoint-names", vars);

                    if let &Operator::Or = op {
                        only_via_map.insert("checkpoint-or", vec![String::from("true")]);
                    }
                }
                // no operator, so just a single variable intro in the vector
                None => {
                    let (checkpoint_var, compiled_checkpoint_intro) =
                        compile_variable_intro(handlebars, &checkpoint_intro.1[0], false);
                    map.insert("intro", compiled_checkpoint_intro);
                    let only_via_intro = render_template(handlebars, &map, Template::OnlyViaIntro);
                    map.remove_entry("var-definition");
                    only_via_map.insert("checkpoint-intros", vec![only_via_intro]);
                    only_via_map.insert("checkpoint-names", vec![checkpoint_var]);
                }
            }

            render_only_via_template(handlebars, &only_via_map)
        }
        ASTNode::JoinedNodes(obligation) => {
            let src_res = compile_ast_node(handlebars, &obligation.src, counter);
            map.insert("src", src_res);
            let sink_res = compile_ast_node(handlebars, &obligation.sink, counter);
            map.insert("sink", sink_res);
            map.insert("counter", counter.to_string());
            *counter += 1;
            render_template(handlebars, &map, node.into())
        }
        ASTNode::Clause(clause) => {
            let variable_intro = match &clause.intro {
                ClauseIntro::ForEach(intro) | ClauseIntro::ThereIs(intro) => {
                    let (variable, variable_intro) =
                        compile_variable_intro(handlebars, intro, false);
                    map.insert("var", variable);
                    // if we're referring to a definition
                    if matches!(intro.intro, VariableIntroType::Variable) {
                        map.insert("lifted", "true".to_string());
                    }
                    variable_intro
                }
                ClauseIntro::Conditional(relation) => compile_relation(handlebars, relation),
            };

            map.insert("intro", variable_intro);
            let body = compile_ast_node(handlebars, &clause.body, counter);
            map.insert("body", body);
            render_template(handlebars, &map, node.into())
        }
        ASTNode::FusedClause(fused_clause) => {
            map.insert("outer_var", fused_clause.outer_var.clone());
            map.insert("inner_var", fused_clause.filter.variable.clone());
            let VariableIntroType::VariableMarked {
                ref marker,
                on_type: _,
            } = fused_clause.filter.intro
            else {
                unreachable!()
            };
            map.insert("marker", marker.clone());
            map.insert("conditional", fused_clause.is_conditional.to_string());

            dbg!(&fused_clause);
            if let Some(rest) = &fused_clause.rest {
                let rest = compile_ast_node(handlebars, rest, counter);
                dbg!(&rest);
                map.insert("rest", rest);
            }

            render_template(handlebars, &map, node.into())
        }
    }
}

fn compile_definition(
    handlebars: &mut Handlebars,
    definition: &Definition,
    policy_scope: &PolicyScope,
) -> String {
    let mut map: HashMap<&str, String> = HashMap::new();
    let (_, variable_intro) = compile_variable_intro(
        handlebars,
        &VariableIntro {
            variable: definition.variable.clone(),
            intro: definition.declaration.intro.clone(),
        },
        true,
    );
    map.insert("inner_var", definition.declaration.variable.clone());
    map.insert("var", definition.variable.clone());
    map.insert("intro", variable_intro);
    map.insert("lifted", "true".to_string());
    let mut counter = 0;
    if let Some(filter) = &definition.filter {
        let filter = compile_ast_node(handlebars, filter, &mut counter);
        map.insert("filter", filter);
    }

    // what to return if creating the node cluster fails, i.e. there are no nodes that fit the definition
    let short_circuit_bool = if let Some(og_clause_intro_typ) = definition.lifted_from {
        matches!(og_clause_intro_typ, OgClauseIntroType::ForEach)
            && matches!(policy_scope, PolicyScope::Everywhere)
    } else {
        true
    };
    map.insert("short-circuit", short_circuit_bool.to_string());

    if let DefinitionScope::Everywhere = definition.scope {
        render_template(handlebars, &map, Template::GlobalDefinition)
    } else {
        render_template(handlebars, &map, Template::Definition)
    }
}

fn compile_definitions(
    handlebars: &mut Handlebars,
    definitions: &[Definition],
    policy_scope: &PolicyScope,
) -> String {
    // Definitions use their own environment so that each definition only knows about the definition(s) above it.
    // This is important if the filter in one definition uses the same variable name as the name of a later definition;
    // the filter variable shouldn't reference the later definition.
    let mut env = Environment::new();
    let mut results = vec![];

    // should be compiling everything in the same order it was declared
    // so that the env doesn't reference stuff that's declared later
    for definition in definitions {
        let result = compile_definition(handlebars, definition, policy_scope);
        let def = VarContext {
            typ: (&definition.declaration).into(),
            is_definition: true,
        };
        env.push((definition.variable.clone(), def));

        results.push(result);
    }

    results.join("\n")
}

pub fn compile(policy: Policy, policy_name: &str, out: &Path, create_bin: bool) -> Result<()> {
    let mut handlebars = Handlebars::new();
    handlebars.set_strict_mode(true);
    register_templates(&mut handlebars);

    // compile definitions & policy
    let mut map: HashMap<&str, String> = HashMap::new();
    let (global_definitions, ctrler_definitions): (Vec<_>, Vec<_>) = policy
        .definitions
        .into_iter()
        .partition(|def| matches!(def.scope, DefinitionScope::Everywhere));
    let compiled_global_definitions =
        compile_definitions(&mut handlebars, &global_definitions, &policy.scope);
    let compiled_ctrler_definitions =
        compile_definitions(&mut handlebars, &ctrler_definitions, &policy.scope);
    map.insert("global-definitions", compiled_global_definitions);
    map.insert("definitions", compiled_ctrler_definitions);

    let mut counter = 0;
    let compiled_body = compile_ast_node(&mut handlebars, &policy.body, &mut counter);
    map.insert("body", compiled_body);

    // render final policy
    if let PolicyScope::InCtrler(ref ctrler) = policy.scope {
        map.insert("ctrler", ctrler.to_string());
    }
    let compiled_scope = render_template(&mut handlebars, &map, policy.scope.into());
    map.insert("policy", compiled_scope);
    let compiled_policy = render_template(&mut handlebars, &map, Template::Base);

    let main = if create_bin {
        let mut main_map = HashMap::new();
        main_map.insert("policy", compiled_policy);
        main_map.insert("policy-file", policy_name.to_string());
        render_template(&mut handlebars, &main_map, Template::Main)
    } else {
        compiled_policy
    };

    fs::write(out, &main)?;
    Command::new("rustfmt").arg(out).status()?;
    Ok(())
}
