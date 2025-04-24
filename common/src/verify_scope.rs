use crate::ast::*;

pub type Environment = Vec<(Variable, VarContext)>;

// context to add to the environment for each variable: was it introduced as a type?
// used for error checking
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum VarContextType {
    Root,
    Item,
    Type,
    SourceOf,
    VarMarked,
}

#[derive(Debug, PartialEq, Eq)]
pub struct VarContext {
    typ: VarContextType,
    pub is_definition: bool,
}

impl From<&mut VarContextType> for &str {
    fn from(value: &mut VarContextType) -> Self {
        match *value {
            VarContextType::Root => "as root",
            VarContextType::Item => "as item",
            VarContextType::Type => "as type",
            VarContextType::SourceOf => "as source of",
            VarContextType::VarMarked => "as a variable marked",
        }
    }
}

impl From<VarContextType> for &str {
    fn from(value: VarContextType) -> Self {
        match value {
            VarContextType::Root => "as root",
            VarContextType::Item => "as item",
            VarContextType::Type => "as type",
            VarContextType::SourceOf => "as source of",
            VarContextType::VarMarked => "as a variable marked",
        }
    }
}

impl From<&VariableIntro> for VarContextType {
    fn from(value: &VariableIntro) -> Self {
        match &value.intro {
            VariableIntroType::Roots => VarContextType::Root,
            VariableIntroType::AllNodes => VarContextType::Item,
            VariableIntroType::VariableMarked { on_type, .. } => {
                if *on_type {
                    VarContextType::Type
                } else {
                    VarContextType::VarMarked
                }
            }
            VariableIntroType::VariableSourceOf(_) => VarContextType::SourceOf,
            _ => unimplemented!("no var context for this type of variable intro"),
        }
    }
}

// variables must go out of scope once we reach an expression on the same level
pub fn remove_from_env(env: &mut Environment, len_before: usize) {
    while env.len() > len_before {
        env.pop();
    }
}

// variable must be in environment before using it
pub fn verify_var_in_scope(var: &Variable, env: &Environment) {
    let present = env.iter().any(|(existing_var, _)| var == existing_var);
    if !present {
        panic!("Must introduce variable {} before using it.\n", var);
    }
}

// variable must not already be in environment before introducing it (i.e., no duplicate variable declarations)
pub fn verify_var_not_in_scope(var: &Variable, env: &Environment) {
    let mut context = None;
    for (existing_var, existing_context) in env {
        if var == existing_var {
            context = Some(existing_context);
            break;
        }
    }
    if context.is_some() {
        let context_str: &str = context.unwrap().typ.into();
        panic!(
            "Duplicate introduction of variable {}; previously introduced {}.\n",
            var, context_str
        );
    }
}

pub fn verify_variable_intro_scope(intro: &VariableIntro, env: &mut Environment) {
    let var = &intro.variable;
    match &intro.intro {
        VariableIntroType::Variable => {
            // if referring to a variable by itself, must already be in the environment
            verify_var_in_scope(var, env);
        }
        VariableIntroType::Roots
        | VariableIntroType::AllNodes
        | VariableIntroType::VariableMarked { .. } => {
            verify_var_not_in_scope(var, env);
            let def = VarContext {
                typ: intro.into(),
                is_definition: false,
            };
            env.push((var.into(), def));
        }
        VariableIntroType::VariableSourceOf(type_var) => {
            verify_var_not_in_scope(var, env);
            let mut present = false;
            for (existing_var, context) in &mut *env {
                if existing_var == type_var {
                    present = true;
                    if context.typ != VarContextType::Type {
                        let context_str: &str = context.typ.into();
                        panic!("To reference sources of {}, must previously introduce it as a type; was previously introduced as {}", type_var, context_str);
                    }
                }
            }
            if !present {
                panic!("Tried to introduce {} as a source of {}, but {} was not previously introduced as a type", type_var, var, type_var);
            }

            let def = VarContext {
                typ: intro.into(),
                is_definition: false,
            };

            env.push((var.into(), def));
        }
    };
}

pub fn verify_relation_scope(relation: &Relation, env: &mut Environment) {
    match relation {
        Relation::Binary { left, right, .. } => {
            verify_var_in_scope(left, env);
            verify_var_in_scope(right, env);
        }
        Relation::IsMarked(var, _) => {
            verify_var_in_scope(var, env);
        }
        Relation::Negation(inner) => {
            verify_relation_scope(inner, env);
        }
    };
}

// Verify that the policy is structured properly, i.e., that every variable is in scope (introduced in a clause) before being referenced in a relation.
pub fn verify_scope(node: &ASTNode, env: &mut Environment) {
    match node {
        ASTNode::Relation(relation) => {
            verify_relation_scope(relation, env);
        }
        ASTNode::OnlyVia(src_intro, sink_intro, checkpoint_intro) => {
            let env_size_before = env.len();
            verify_variable_intro_scope(src_intro, env);
            for intro in &checkpoint_intro.1 {
                verify_variable_intro_scope(intro, env);
            }
            for intro in &sink_intro.1 {
                verify_variable_intro_scope(intro, env);
            }
            remove_from_env(env, env_size_before);
        }
        ASTNode::JoinedNodes(obligation) => {
            verify_scope(&obligation.src, env);
            verify_scope(&obligation.sink, env);
        }
        ASTNode::Clause(clause) => {
            let env_size_before_clause = env.len();
            match &clause.intro {
                ClauseIntro::ForEach(intro) | ClauseIntro::ThereIs(intro) => {
                    verify_variable_intro_scope(intro, env)
                }
                ClauseIntro::Conditional(relation) => verify_relation_scope(relation, env),
            };
            verify_scope(&clause.body, env);

            // variables introduced in this clause must go out of scope once it ends
            remove_from_env(env, env_size_before_clause);
        }
    }
}

pub fn verify_definitions_scope(definitions: &Vec<Definition>, env: &mut Environment) {
    for definition in definitions {
        let env_size_before_definition = env.len();
        verify_variable_intro_scope(&definition.declaration, env);
        if let Some(filter) = &definition.filter {
            verify_scope(filter, env);
        }
        // variables introduced in this definition must go out of scope once it ends
        remove_from_env(env, env_size_before_definition);
        // reasoning here is that this the variable under which the definition is declared, and everything else is just internal irrelevant stuff
        let def = VarContext {
            typ: (&definition.declaration).into(),
            is_definition: true,
        };
        env.push((definition.variable.clone(), def));
    }
}
