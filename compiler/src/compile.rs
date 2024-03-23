use handlebars::{no_escape, Handlebars};
use parsers::{ASTNode, Variable, Marker, Relation, ClauseIntro, VariableIntro, Operator};
use std::collections::{HashMap, HashSet};
use std::{fs, vec, env};
use std::io::Result;

use crate::templates::{register, render};

// context to add to the environment for each variable: was it introduced as a type?
// used for error-checking -- if policy tries to reference a source of a variable but it wasn't
// introduced as a type, throw an error
// TODO may be useful to add more context here, but for now this binary type/not type distinction is all I need
#[derive(PartialEq, Eq)]
enum VarContext {
    AsType,
    AsSourceOf,
    AsVarMarked,
}

impl From<&VarContext> for &str {
    fn from(value: &VarContext) -> Self {
        match value {
            VarContext::AsType => "as type",
            VarContext::AsSourceOf => "as source of",
            VarContext::AsVarMarked => "as a variable marked",
        }
    }
}

fn verify_var_in_scope<'a>(var : &Variable<'a>, env : &Vec<(Variable<'a>, VarContext)>) {
    let present = env.iter().any(|(existing_var, context)| var == existing_var);
    if !present {
        panic!("Must introduce variable {} before using it.\n", var);
    }
}

fn compile_variable_intro<'a>(
    handlebars: &mut Handlebars,
    intro: &VariableIntro<'a>,
    map: &mut HashMap<&str, &str>,
    env: &Vec<(Variable<'a>, VarContext)>,
) { 
    match intro {
        VariableIntro::Roots => {},
        VariableIntro::Variable(var) => {
            // if referring to a variable by itself, must already be in the environment
            verify_var_in_scope(var, env);
            map.insert("var", var);
        },
        VariableIntro::VariableMarked((var, marker)) => {
            map.insert("var", var);
            map.insert("marker", marker);
            env.push((var, VarContext::AsVarMarked));
        }
        VariableIntro::VariableOfTypeMarked((var, marker)) => {
            map.insert("var", var);
            map.insert("marker", marker);
            env.push((var, VarContext::AsType));   
        },
        VariableIntro::VariableSourceOf((var, type_var)) => {
            let mut present = false;
            for (existing_var, context) in env {
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

            map.insert("var", var);
            map.insert("type-var", type_var);
            env.push((var, VarContext::AsSourceOf));
        }
    };
}

// when handling not case, just append ! to the front
fn compile_relation<'a>(
    handlebars: &mut Handlebars,
    relation: &Relation<'a>, 
    map: &mut HashMap<&str, &str>,
    env: &Vec<(Variable<'a>, VarContext)>,
) { 
    match relation {
        Relation::Influences((var_source, var_dest)) | 
        Relation::DoesNotInfluence((var_source, var_dest)) |
        Relation::FlowsTo((var_source, var_dest)) |
        Relation::NoFlowsTo((var_source, var_dest)) |
        Relation::ControlFlow((var_source, var_dest)) |
        Relation::NoControlFlow((var_source, var_dest)) | 
        Relation::AssociatedCallSite((var_source, var_dest))  => {
            verify_var_in_scope(var_source, env);
            verify_var_in_scope(var_dest, env);
            map.insert("src", *var_source);
            map.insert("dest", *var_dest);
        },
        Relation::IsMarked((var, marker)) | Relation::IsNotMarked((var, marker)) => {
            verify_var_in_scope(var, env);
            map.insert("src", *var);
            map.insert("marker", *marker);
        },
        Relation::OnlyVia((src_intro, dest_intro, checkpoint_intro)) => {
            compile_variable_intro(handlebars, src_intro, map, env);
            let src = render(handlebars, &map, (*src_intro).into());
            compile_variable_intro(handlebars, dest_intro, map, env);
            let dest = render(handlebars, &map, (*dest_intro).into());
            compile_variable_intro(handlebars, checkpoint_intro, map, env);
            let checkpoint = render(handlebars, &map, (*checkpoint_intro).into());
            map.insert("src", &src);
            map.insert("dest", &dest);
            map.insert("checkpoint", &checkpoint);
        }
    };
}

fn traverse_ast<'a>(
    handlebars: &mut Handlebars,
    node: &ASTNode<'a>,
    env: &mut Vec<(Variable<'a>, VarContext)>,
) -> String {
    let mut map: HashMap<&str, &str> = HashMap::new();
    match node {
        ASTNode::Relation(relation) => {
            compile_relation(handlebars, relation, &mut map, env);
            render(handlebars, &map, (*relation).into())
        },
        ASTNode::JoinedNodes(obligation) => {
            let src_res = &traverse_ast(handlebars, &obligation.src, env);
            map.insert("src", src_res);
            let dest_res = &traverse_ast(handlebars, &obligation.dest, env);
            map.insert("dest", dest_res);
            render(handlebars, &map, obligation.op.into())
        }
        ASTNode::Clause(clause) => {
            let env_size_before_clause = env.len();
            match clause.intro {
                ClauseIntro::ForEach(intro) | ClauseIntro::ThereIs(intro) => compile_variable_intro(handlebars, &intro, &mut map, env),
                ClauseIntro::Conditional(relation) => compile_relation(handlebars, &relation, &mut map, env)
            };
            let body = traverse_ast(handlebars, &clause.body, env);
            map.insert("body", &body);
            
            // variables introduced in this clause must go out of scope once it ends
            while env.len() > env_size_before_clause {
                env.pop();
            }

            // TODO there may be some weirdness with the map keys for the clause intro and bodies overlapping if you wait to evaluate
            // until the end like this...
            // i think you may have a problem with multiple relations using "src" and "dest"

            render(handlebars, &map, clause.intro.into())
            
        },
    }
}

fn compile_policy<'a>(
    handlebars: &mut Handlebars,
    policy: Policy<'a>,
) -> Result<()> {
    let mut env: HashMap<Variable<'a>, Marker<'a>> = HashMap::new();
    let obligation = traverse_ast(handlebars, &policy.body, &mut env);
    
    let mut nodes_map: HashMap<&str, HashMap<Variable<'a>, Marker<'a>>> = HashMap::new();
    nodes_map.insert("bindings", env);
    let nodes = render_template(handlebars, &nodes_map, NODES_TEMPLATE);

    let mut map: HashMap<&str, &str> = HashMap::new();
    map.insert("nodes", &nodes);
    map.insert("obligation", &obligation);
    let policy_logic = render_template(handlebars, &map, scope_to_template(&policy.scope));
    map.clear();

    map.insert("policy", &policy_logic);
    let res = render_template(handlebars, &map, BASE_TEMPLATE);

    fs::write("compiled-policy.rs", &res)?;
    Ok(())
}

pub fn compile<'a>(policy: Policy<'a>) -> Result<()> {
    let mut handlebars = Handlebars::new();
    handlebars.register_escape_fn(no_escape);
    register_templates(&mut handlebars);
    compile_policy(&mut handlebars, policy)
}
