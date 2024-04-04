use handlebars::Handlebars;
use parsers::{ASTNode, Variable, Relation, ClauseIntro, VariableIntro, Policy, Definition, PolicyScope};
use std::collections::HashMap;
use std::fs;
use std::io::Result;

use templates::{register_templates, render_template, Template};
use crate::verify_scope::{VarContext, verify_definitions_scope, verify_scope};

fn compile_variable_intro(
    handlebars: &mut Handlebars,
    intro: &VariableIntro,
    map: &mut HashMap<&str, String>,
) -> (String, String) {
    match intro {
         VariableIntro::Roots(var) | VariableIntro::AllNodes(var) | VariableIntro::Variable(var) => {
            map.insert("var", var.into());
        },
        VariableIntro::VariableMarked((var, marker)) | VariableIntro::VariableOfTypeMarked((var, marker)) => {
            map.insert("var", var.into());
            map.insert("marker", marker.into());
        },
        VariableIntro::VariableSourceOf((var, type_var)) => {
            map.insert("var", var.into());
            map.insert("type-var", type_var.into());
        }
    };
    let variable : String = match intro {
        VariableIntro::Roots(var) |
        VariableIntro::AllNodes(var) |
        VariableIntro::Variable(var) |
        VariableIntro::VariableMarked((var, _)) |
        VariableIntro::VariableOfTypeMarked((var, _)) |
        VariableIntro::VariableSourceOf((var, _)) => var.into(),
    };
    (variable, render_template(handlebars, &map, intro.into()))
}

fn compile_relation(
    handlebars: &mut Handlebars,
    relation: &Relation, 
    map: &mut HashMap<&str, String>,
) -> String { 
    match relation {
        Relation::Influences((var_source, var_sink)) | 
        Relation::DoesNotInfluence((var_source, var_sink)) |
        Relation::FlowsTo((var_source, var_sink)) |
        Relation::NoFlowsTo((var_source, var_sink)) |
        Relation::ControlFlow((var_source, var_sink)) |
        Relation::NoControlFlow((var_source, var_sink)) | 
        Relation::AssociatedCallSite((var_source, var_sink))  => {
            map.insert("src", var_source.into());
            map.insert("sink", var_sink.into());
        },
        Relation::IsMarked((var, marker)) | Relation::IsNotMarked((var, marker)) => {
            map.insert("src", var.into());
            map.insert("marker", marker.into());
        }, 
    };
    render_template(handlebars, &map, relation.into())
}

// for joined nodes, we don't know how many expressions we're and/oring together in the whole policy,
// so use the counter to give each variable a unique name -- see and/or templates for more context
fn compile_ast_node(
    handlebars: &mut Handlebars,
    node: &ASTNode,
    counter: &mut u32
) -> String {
    let mut map: HashMap<&str, String> = HashMap::new();
    match node {
        ASTNode::Relation(relation) => {
            compile_relation(handlebars, relation, &mut map)
        },
        ASTNode::OnlyVia((src_intro, sink_intro, checkpoint_intro)) => {
            let (src_var, compiled_src_intro) = compile_variable_intro(handlebars, src_intro, &mut map);
            let (sink_var, compiled_sink_intro) = compile_variable_intro(handlebars, sink_intro, &mut map);
            let (checkpoint_var, compiled_checkpoint_intro) = compile_variable_intro(handlebars, checkpoint_intro, &mut map);
            map.insert("src", src_var);
            map.insert("sink", sink_var);
            map.insert("checkpoint", checkpoint_var);
            map.insert("src_intro", compiled_src_intro);
            map.insert("sink_intro", compiled_sink_intro);
            map.insert("checkpoint_intro", compiled_checkpoint_intro);
            render_template(handlebars, &map, node.into())
        },
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
                    let (variable, variable_intro) = compile_variable_intro(handlebars, &intro, &mut map);
                    map.insert("var", variable);
                    variable_intro
                },
                ClauseIntro::Conditional(relation) => {
                    compile_relation(handlebars, &relation, &mut map)
                }
            };
            
            map.insert("intro", variable_intro);

            let body = compile_ast_node(handlebars, &clause.body, counter);
            map.insert("body", body);
            render_template(handlebars, &map, node.into())
        },
    }
}

fn compile_definitions(
    handlebars: &mut Handlebars,
    definitions: &Vec<Definition>,
) -> String {
    let mut map : HashMap<&str, String> = HashMap::new();
    let mut results : Vec<String> = Vec::new();
    for definition in definitions {
        let (inner_var, variable_intro) = compile_variable_intro(handlebars, &definition.declaration, &mut map);
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

pub fn compile(policy: Policy) -> Result<()> {
    let mut handlebars = Handlebars::new();
    register_templates(&mut handlebars);
    
    // verify that variables in definitions & policy are properly scoped
    let mut env: Vec<(Variable, VarContext)> = Vec::new();
    verify_definitions_scope(&policy.definitions, &mut env);
    verify_scope(&policy.body, &mut env);
    
    // compile definitions & policy
    let mut map : HashMap<&str, String> = HashMap::new();
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
    let compiled_policy = render_template(&mut handlebars, &map, Template::Base);

    fs::write("compiled-policy.rs", &compiled_policy)?;
    Ok(())
}
