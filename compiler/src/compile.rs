use handlebars::Handlebars;
use parsers::{ASTNode, Variable, Relation, ClauseIntro, VariableIntro, Policy};
use std::collections::HashMap;
use std::fs;
use std::io::Result;

use templates::{register_templates, render_template};

// context to add to the environment for each variable: was it introduced as a type?
// used for error-checking -- if policy tries to reference a source of a variable but it wasn't
// introduced as a type, throw an error
// TODO may be useful to add more context here, but for now this binary type/not type distinction is all I need
#[derive(PartialEq, Eq, Clone, Copy)]
enum VarContext {
    AsType,
    AsSourceOf,
    AsVarMarked,
}

impl From<VarContext> for &str {
    fn from(value: VarContext) -> Self {
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

fn verify_variable_intro_scope<'a>(
    intro: &VariableIntro<'a>,
    env: &mut Vec<(Variable<'a>, VarContext)>,
) { 
    // TODO verify that you're not introducing a variable that's already been introduced
    match intro {
        VariableIntro::Roots => {},
        VariableIntro::Variable(var) => {
            // if referring to a variable by itself, must already be in the environment
            verify_var_in_scope(var, env);
        },
        VariableIntro::VariableMarked((var, _)) => {
            env.push((var, VarContext::AsVarMarked));
        }
        VariableIntro::VariableOfTypeMarked((var, _)) => {
            env.push((var, VarContext::AsType));   
        },
        VariableIntro::VariableSourceOf((var, type_var)) => {
            let mut present = false;
            // TODO this &mut *env is weird... is this really the best way of doing it?
            // just need to be able to push var at the end w/o moving the value here
            for (existing_var, context) in &mut *env {
                if existing_var == type_var {
                    present = true;
                    if *context != VarContext::AsType {
                        // TODO I suspect there is a more idiomatic way of handling this context --> string transformation
                        let context_str : &str = (*context).into();
                        panic!("To reference sources of {}, must previously introduce it as a type; was previously introduced as {}", type_var, context_str);
                    }
                }
            }
            if !present {
                panic!("Tried to introduce {} as a source of {}, but {} was not previously introduced as a type", type_var, var, type_var);
            }

            env.push((var, VarContext::AsSourceOf));
        }
    };
}

fn verify_relation_scope<'a>(
    relation: &Relation<'a>, 
    env: &mut Vec<(Variable<'a>, VarContext)>,
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
        },
        Relation::IsMarked((var, marker)) | Relation::IsNotMarked((var, marker)) => {
            verify_var_in_scope(var, env);
        },
        Relation::OnlyVia((src_intro, dest_intro, checkpoint_intro)) => {
            verify_variable_intro_scope(src_intro, env);
            verify_variable_intro_scope(dest_intro, env);
            verify_variable_intro_scope(checkpoint_intro, env);
        }
    };
}

// Verify that the policy is structured properly, i.e., that every variable is in scope (introduced in a clause) before being referenced in a relation.
fn verify_scope<'a>(
    node: &ASTNode<'a>,
    env: &mut Vec<(Variable<'a>, VarContext)>,
) {
    let mut map: HashMap<&str, &str> = HashMap::new();
    match node {
        ASTNode::Relation(relation) => {
            verify_relation_scope(relation, env);
        },
        ASTNode::JoinedNodes(obligation) => {
            verify_scope(&obligation.src, env);
            verify_scope(&obligation.dest, env);
        }
        ASTNode::Clause(clause) => {
            let env_size_before_clause = env.len();
            match &clause.intro {
                ClauseIntro::ForEach(intro) | ClauseIntro::ThereIs(intro) => verify_variable_intro_scope(&intro, env),
                ClauseIntro::Conditional(relation) => verify_relation_scope(&relation, env),
            };
            verify_scope(&clause.body, env);

            // variables introduced in this clause must go out of scope once it ends
            while env.len() > env_size_before_clause {
                env.pop();
            }
        },
    }
}

fn compile_variable_intro<'a>(
    handlebars: &mut Handlebars,
    intro: &VariableIntro<'a>,
    map: &mut HashMap<&str, &str>,
) -> String { 
    match intro {
        VariableIntro::Roots => {},
        VariableIntro::Variable(var) => {
            map.insert("var", var);
        },
        VariableIntro::VariableMarked((var, marker)) => {
            map.insert("var", var);
            map.insert("marker", marker);
        }
        VariableIntro::VariableOfTypeMarked((var, marker)) => {
            map.insert("var", var);
            map.insert("marker", marker);  
        },
        VariableIntro::VariableSourceOf((var, type_var)) => {
            map.insert("var", var);
            map.insert("type-var", type_var);
        }
    };
    render_template(handlebars, &map, (*intro).into())
}

fn compile_relation<'a>(
    handlebars: &mut Handlebars,
    relation: &Relation<'a>, 
    map: &mut HashMap<&str, &str>,
) -> String { 
    match relation {
        Relation::Influences((var_source, var_dest)) | 
        Relation::DoesNotInfluence((var_source, var_dest)) |
        Relation::FlowsTo((var_source, var_dest)) |
        Relation::NoFlowsTo((var_source, var_dest)) |
        Relation::ControlFlow((var_source, var_dest)) |
        Relation::NoControlFlow((var_source, var_dest)) | 
        Relation::AssociatedCallSite((var_source, var_dest))  => {
            map.insert("src", *var_source);
            map.insert("dest", *var_dest);
        },
        Relation::IsMarked((var, marker)) | Relation::IsNotMarked((var, marker)) => {
            map.insert("src", *var);
            map.insert("marker", *marker);
        },
        Relation::OnlyVia((src_intro, dest_intro, checkpoint_intro)) => {
            compile_variable_intro(handlebars, src_intro, map);
            let src = render_template(handlebars, &map, (*src_intro).into());
            compile_variable_intro(handlebars, dest_intro, map);
            let dest = render_template(handlebars, &map, (*dest_intro).into());
            compile_variable_intro(handlebars, checkpoint_intro, map);
            let checkpoint = render_template(handlebars, &map, (*checkpoint_intro).into());
            map.insert("src", &src);
            map.insert("dest", &dest);
            map.insert("checkpoint", &checkpoint);
        }
    };
    render_template(handlebars, &map, (*relation).into())
}

fn generate<'a>(
    handlebars: &mut Handlebars,
    node: &ASTNode<'a>,
) -> String {
    let mut map: HashMap<&str, &str> = HashMap::new();
    match node {
        ASTNode::Relation(relation) => {
            compile_relation(handlebars, relation, &mut map);
            render_template(handlebars, &map, (*relation).into())
        },
        ASTNode::JoinedNodes(obligation) => {
            let src_res = &generate(handlebars, &obligation.src);
            map.insert("src", src_res);
            let dest_res = &generate(handlebars, &obligation.dest);
            map.insert("dest", dest_res);
            render_template(handlebars, &map, obligation.op.into())
        }
        ASTNode::Clause(clause) => {
            let body = generate(handlebars, &clause.body);
            map.insert("body", &body);

            let variable_intro = match clause.intro {
                ClauseIntro::ForEach(intro) | ClauseIntro::ThereIs(intro) => compile_variable_intro(handlebars, &intro, &mut map),
                ClauseIntro::Conditional(relation) => compile_relation(handlebars, &relation, &mut map)
            };
            map.insert("intro", &variable_intro);

            render_template(handlebars, &map, clause.intro.into())
        },
    }
}

fn compile_policy<'a>(
    handlebars: &mut Handlebars,
    policy: Policy<'a>,
) -> Result<()> {
    let mut env: Vec<(Variable<'a>, VarContext)> = Vec::new();
    // TODO add definitions to the environment
    verify_scope(&policy.body, &mut env);
    // TODO render_template definitions
    // TODO render_template scope -- this can't be part of generate() bc it's recursive
    // the policy body should be inside the scope template (since scope is just iterating over the controllers and contains everything)
    // so should render_template definitions and policy body, then add both of those to a map
    // then render_template the template for the scope given that map
    // so something like:
    // <scope template>
    // for ctrler in ctrlers {
    //      {definitions}
    //      {body}
    //}

    let policy_str = generate(handlebars, &policy.body);

    fs::write("compiled-policy.rs", &policy_str)?;
    Ok(())
}

pub fn compile<'a>(policy: Policy<'a>) -> Result<()> {
    let mut handlebars = Handlebars::new();
    register_templates(&mut handlebars);
    compile_policy(&mut handlebars, policy)
}
