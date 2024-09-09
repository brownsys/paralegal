use handlebars::Handlebars;
use parsers::{
    ASTNode, ClauseIntro, Definition, DefinitionScope, Operator, Policy, PolicyScope, Relation,
    Variable, VariableIntro,
};
use std::fs;
use std::io::Result;
use std::{collections::HashMap, path::Path};

use crate::verify_scope::{verify_definitions_scope, verify_scope, VarContext};
use templates::{register_templates, render_only_via_template, render_template, Template};

fn compile_variable_intro(
    handlebars: &mut Handlebars,
    intro: &VariableIntro,
    map: &mut HashMap<&str, String>,
) -> (String, String) {
    match intro {
        VariableIntro::Roots(var) | VariableIntro::AllNodes(var) => {
            map.insert("var", var.into());
        }
        VariableIntro::Variable(var) => {
            map.insert("var", var.into());
            // just insert a non-null string
            map.insert("definition", String::from("true"));
        }
        VariableIntro::VariableMarked((var, marker))
        | VariableIntro::VariableOfTypeMarked((var, marker)) => {
            map.insert("var", var.into());
            map.insert("marker", marker.into());
        }
        VariableIntro::VariableSourceOf((var, type_var)) => {
            map.insert("var", var.into());
            map.insert("type-var", type_var.into());
        }
    };
    let variable: String = match intro {
        VariableIntro::Roots(var)
        | VariableIntro::AllNodes(var)
        | VariableIntro::Variable(var)
        | VariableIntro::VariableMarked((var, _))
        | VariableIntro::VariableOfTypeMarked((var, _))
        | VariableIntro::VariableSourceOf((var, _)) => var.into(),
    };
    (variable, render_template(handlebars, &map, intro.into()))
}

fn compile_relation(
    handlebars: &mut Handlebars,
    relation: &Relation,
    map: &mut HashMap<&str, String>,
) -> String {
    match relation {
        Relation::Influences((var_source, var_sink))
        | Relation::DoesNotInfluence((var_source, var_sink))
        | Relation::FlowsTo((var_source, var_sink))
        | Relation::NoFlowsTo((var_source, var_sink))
        | Relation::ControlFlow((var_source, var_sink))
        | Relation::NoControlFlow((var_source, var_sink))
        | Relation::AssociatedCallSite((var_source, var_sink)) => {
            map.insert("src", var_source.into());
            map.insert("sink", var_sink.into());
        }
        Relation::IsMarked((var, marker)) | Relation::IsNotMarked((var, marker)) => {
            map.insert("src", var.into());
            map.insert("marker", marker.into());
        }
    };
    render_template(handlebars, &map, relation.into())
}

// for joined nodes, we don't know how many expressions we're and/oring together in the whole policy,
// so use the counter to give each variable a unique name -- see and/or templates for more context
fn compile_ast_node(handlebars: &mut Handlebars, node: &ASTNode, counter: &mut u32) -> String {
    let mut map: HashMap<&str, String> = HashMap::new();
    match node {
        ASTNode::Relation(relation) => compile_relation(handlebars, relation, &mut map),
        ASTNode::OnlyVia((src_intro, sink_intro, checkpoint_intro)) => {
            // TODO this logic is overcomplicated and gross
            // but I have an SOSP deadline and it works, so fix later...

            let mut only_via_map: HashMap<&str, Vec<String>> = HashMap::new();

            let (src_var, compiled_src_intro) =
                compile_variable_intro(handlebars, &src_intro, &mut map);
            map.insert("intro", compiled_src_intro);
            let src_intro = render_template(handlebars, &map, Template::OnlyViaIntro);
            map.remove_entry("definition");
            only_via_map.insert("src-intros", vec![src_intro]);
            only_via_map.insert("src", vec![src_var]);

            match &sink_intro.0 {
                // an operator is present, so there are multiple variable intros in the vector
                Some(op) => {
                    let mut compiled_intros: Vec<String> = vec![];
                    let mut vars: Vec<String> = vec![];
                    for intro in &sink_intro.1 {
                        let (sink_var, compiled_sink_intro) =
                            compile_variable_intro(handlebars, &intro, &mut map);
                        map.insert("intro", compiled_sink_intro);
                        let only_via_intro =
                            render_template(handlebars, &map, Template::OnlyViaIntro);
                        map.remove_entry("definition");
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
                        compile_variable_intro(handlebars, &sink_intro.1[0], &mut map);
                    map.insert("intro", compiled_sink_intro);
                    let only_via_intro = render_template(handlebars, &map, Template::OnlyViaIntro);
                    map.remove_entry("definition");
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
                        let (sink_var, compiled_checkpoint_intro) =
                            compile_variable_intro(handlebars, &intro, &mut map);
                        map.insert("intro", compiled_checkpoint_intro);
                        let only_via_intro =
                            render_template(handlebars, &map, Template::OnlyViaIntro);
                        map.remove_entry("definition");
                        compiled_intros.push(only_via_intro);
                        vars.push(sink_var);
                    }
                    only_via_map.insert("checkpoint-intros", compiled_intros);
                    only_via_map.insert("checkpoint-names", vars);

                    if let &Operator::Or = op {
                        only_via_map.insert("checkpoint-or", vec![String::from("true")]);
                    }
                }
                // no operator, so just a single variable intro in the vector
                None => {
                    let (checkpoint_var, compiled_sink_intro) =
                        compile_variable_intro(handlebars, &sink_intro.1[0], &mut map);
                    map.insert("intro", compiled_sink_intro);
                    let only_via_intro = render_template(handlebars, &map, Template::OnlyViaIntro);
                    map.remove_entry("definition");
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
                        compile_variable_intro(handlebars, &intro, &mut map);
                    map.insert("var", variable);
                    variable_intro
                }
                ClauseIntro::Conditional(relation) => {
                    compile_relation(handlebars, &relation, &mut map)
                }
            };

            map.insert("intro", variable_intro);

            let body = compile_ast_node(handlebars, &clause.body, counter);
            map.insert("body", body);
            render_template(handlebars, &map, node.into())
        }
    }
}

fn compile_definitions(handlebars: &mut Handlebars, definitions: &Vec<Definition>) -> String {
    let mut map: HashMap<&str, String> = HashMap::new();
    let mut results: Vec<String> = Vec::new();
    for definition in definitions {
        if let DefinitionScope::Everywhere = definition.scope {
            map.insert("everywhere", String::from("true"));
        }
        let (inner_var, variable_intro) =
            compile_variable_intro(handlebars, &definition.declaration, &mut map);
        map.insert("inner_var", inner_var);
        map.insert("var", definition.variable.clone());
        map.insert("intro", variable_intro);
        let mut counter = 0;
        let filter = compile_ast_node(handlebars, &definition.filter, &mut counter);
        map.insert("filter", filter);
        let result = render_template(handlebars, &map, Template::Definition);
        results.push(result);
    }

    return results.join("\n");
}

pub fn compile(policy: Policy, out: &Path, create_bin: bool) -> Result<()> {
    let mut handlebars = Handlebars::new();
    register_templates(&mut handlebars);

    // verify that variables in definitions & policy are properly scoped
    let mut env: Vec<(Variable, VarContext)> = Vec::new();
    verify_definitions_scope(&policy.definitions, &mut env);
    verify_scope(&policy.body, &mut env);

    // compile definitions & policy
    let mut map: HashMap<&str, String> = HashMap::new();
    let compiled_definitions = compile_definitions(&mut handlebars, &policy.definitions);
    map.insert("definitions", compiled_definitions);
    let mut counter = 0;
    let compiled_body = compile_ast_node(&mut handlebars, &policy.body, &mut counter);
    map.insert("body", compiled_body);

    // render final policy
    if let PolicyScope::InCtrler(ref ctrler) = policy.scope {
        map.insert("ctrler", ctrler.to_string());
    }
    let compiled_scope = render_template(&mut handlebars, &map, policy.scope.into());
    map.insert("policy", compiled_scope);
    let compiled_policy = render_template(
        &mut handlebars,
        &map,
        if create_bin {
            Template::Main
        } else {
            Template::Base
        },
    );

    fs::write(out, &compiled_policy)?;
    Ok(())
}
