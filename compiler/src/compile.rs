use handlebars::Handlebars;
use parsers::{ASTNode, Variable, Relation, ClauseIntro, VariableIntro, Policy, Definition, PolicyScope};
use std::collections::HashMap;
use std::fs;
use std::io::Result;

use templates::{register_templates, render_template, Template};

// context to add to the environment for each variable: was it introduced as a type?
// used for error checking
#[derive(Debug, PartialEq, Eq)]
enum VarContext {
    AsRoot,
    AsItem,
    AsType,
    AsSourceOf,
    AsVarMarked,
}

impl From<&mut VarContext> for &str {
    fn from(value: &mut VarContext) -> Self {
        match value {
            &mut VarContext::AsRoot => "as root",
            &mut VarContext::AsItem => "as item",
            &mut VarContext::AsType => "as type",
            &mut VarContext::AsSourceOf => "as source of",
            &mut VarContext::AsVarMarked => "as a variable marked",
        }
    }
}

impl From<&VarContext> for &str {
    fn from(value: &VarContext) -> Self {
        match value {
            &VarContext::AsRoot => "as root",
            &VarContext::AsItem => "as item",
            &VarContext::AsType => "as type",
            &VarContext::AsSourceOf => "as source of",
            &VarContext::AsVarMarked => "as a variable marked",
        }
    }
}

impl From<&VariableIntro> for VarContext {
    fn from(value : &VariableIntro) -> Self {
        match value {
            &VariableIntro::Roots(_) => VarContext::AsRoot,
            &VariableIntro::AllNodes(_) => VarContext::AsItem,
            &VariableIntro::VariableMarked(_) => VarContext::AsVarMarked,
            &VariableIntro::VariableOfTypeMarked(_) => VarContext::AsType,
            &VariableIntro::VariableSourceOf(_) => VarContext::AsSourceOf,
            _ => unimplemented!("no var context for this type of variable intro")
        }
    }
}

// variables must go out of scope once we reach an expression on the same level
fn remove_from_env(env: &mut Vec<(Variable, VarContext)>, len_before: usize) {
     while env.len() > len_before {
        env.pop();
    }
} 

// variable must be in environment before using it
fn verify_var_in_scope(var : &Variable, env : &Vec<(Variable, VarContext)>) {
    let present = env.iter().any(|(existing_var, _)| var == existing_var);
    if !present {
        dbg!(&env);
        panic!("Must introduce variable {} before using it.\n", var);
    }
}

// variable must not already be in environment before introducing it (i.e., no duplicate variable declarations)
fn verify_var_not_in_scope(var : &Variable, env : &Vec<(Variable, VarContext)>) {
    let mut context = None;
    for (existing_var, existing_context) in env {
        if var == existing_var {
            context = Some(existing_context);
            break;
        }
    }
    if context.is_some() {
        dbg!(&env);
        let context_str : &str = context.unwrap().into();
        panic!("Duplicate introduction of variable {}; previously introduced {}.\n", var, context_str);
    }
}

fn verify_variable_intro_scope(
    intro: &VariableIntro,
    env: &mut Vec<(Variable, VarContext)>,
) { 
    match intro {
        VariableIntro::Variable(var) => {
            // if referring to a variable by itself, must already be in the environment
            verify_var_in_scope(var, env);
        },
        VariableIntro::Roots(var) | VariableIntro::AllNodes(var) | VariableIntro::VariableMarked((var, _)) => {
            verify_var_not_in_scope(var, env);
            env.push((var.into(), intro.into()));
        }
        VariableIntro::VariableOfTypeMarked((var, _)) => {
            verify_var_not_in_scope(var, env);
            env.push((var.into(), intro.into()));
        },
        VariableIntro::VariableSourceOf((var, type_var)) => {
            verify_var_not_in_scope(var, env);
            let mut present = false;
            // TODO this &mut *env is weird... is this really the best way of doing it?
            // just need to be able to push var at the end w/o moving the value here
            // I also do not need mutable references to existing_var or context
            for (existing_var, context) in &mut *env {
                if existing_var == type_var {
                    present = true;
                    if *context != VarContext::AsType {
                        let context_str : &str = context.into();
                        panic!("To reference sources of {}, must previously introduce it as a type; was previously introduced as {}", type_var, context_str);
                    }
                }
            }
            if !present {
                panic!("Tried to introduce {} as a source of {}, but {} was not previously introduced as a type", type_var, var, type_var);
            }

            env.push((var.into(), intro.into()));
        }
    };
}

fn verify_relation_scope(
    relation: &Relation, 
    env: &mut Vec<(Variable, VarContext)>,
) { 
    match relation {
        Relation::Influences((var_source, var_sink)) | 
        Relation::DoesNotInfluence((var_source, var_sink)) |
        Relation::FlowsTo((var_source, var_sink)) |
        Relation::NoFlowsTo((var_source, var_sink)) |
        Relation::ControlFlow((var_source, var_sink)) |
        Relation::NoControlFlow((var_source, var_sink)) | 
        Relation::AssociatedCallSite((var_source, var_sink))  => {
            verify_var_in_scope(var_source, env);
            verify_var_in_scope(var_sink, env);
        },
        Relation::IsMarked((var, _)) | Relation::IsNotMarked((var, _)) => {
            verify_var_in_scope(var, env);
        },
    };
}

// Verify that the policy is structured properly, i.e., that every variable is in scope (introduced in a clause) before being referenced in a relation.
fn verify_scope(
    node: &ASTNode,
    env: &mut Vec<(Variable, VarContext)>,
) {
    match node {
        ASTNode::Relation(relation) => {
            verify_relation_scope(relation, env);
        },
        ASTNode::OnlyVia((src_intro, sink_intro, checkpoint_intro)) => {
            let env_size_before = env.len();
            verify_variable_intro_scope(src_intro, env);
            verify_variable_intro_scope(sink_intro, env);
            verify_variable_intro_scope(checkpoint_intro, env);
            remove_from_env(env, env_size_before);
        },
        ASTNode::JoinedNodes(obligation) => {
            verify_scope(&obligation.src, env);
            verify_scope(&obligation.sink, env);
        }
        ASTNode::Clause(clause) => {
            let env_size_before_clause = env.len();
            match &clause.intro {
                ClauseIntro::ForEach(intro) | ClauseIntro::ThereIs(intro) => verify_variable_intro_scope(&intro, env),
                ClauseIntro::Conditional(relation) => verify_relation_scope(&relation, env),
            };
            verify_scope(&clause.body, env);

            // variables introduced in this clause must go out of scope once it ends
            remove_from_env(env, env_size_before_clause);
        },
    }
}

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

fn verify_definitions_scope(
    definitions: &Vec<Definition>,
    env: &mut Vec<(Variable, VarContext)>
) {
    for definition in definitions {
        let env_size_before_definition = env.len();
        verify_variable_intro_scope(&definition.declaration, env);
        verify_scope(&definition.filter, env);
        // variables introduced in this definition must go out of scope once it ends
        remove_from_env(env, env_size_before_definition);
        env.push((definition.variable.clone(), (&definition.declaration).into()));
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
