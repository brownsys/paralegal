use parsers::{ASTNode, Variable, Relation, ClauseIntro, VariableIntro, Definition};

// context to add to the environment for each variable: was it introduced as a type?
// used for error checking
#[derive(Debug, PartialEq, Eq)]
pub enum VarContext {
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
pub fn remove_from_env(env: &mut Vec<(Variable, VarContext)>, len_before: usize) {
     while env.len() > len_before {
        env.pop();
    }
} 

// variable must be in environment before using it
pub fn verify_var_in_scope(var : &Variable, env : &Vec<(Variable, VarContext)>) {
    let present = env.iter().any(|(existing_var, _)| var == existing_var);
    if !present {
        dbg!(&env);
        panic!("Must introduce variable {} before using it.\n", var);
    }
}

// variable must not already be in environment before introducing it (i.e., no duplicate variable declarations)
pub fn verify_var_not_in_scope(var : &Variable, env : &Vec<(Variable, VarContext)>) {
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

pub fn verify_variable_intro_scope(
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

pub fn verify_relation_scope(
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
pub fn verify_scope(
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

pub fn verify_definitions_scope(
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