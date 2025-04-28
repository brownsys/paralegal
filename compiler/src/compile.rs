use common::{ast::*, Policy, PolicyScope};
use handlebars::Handlebars;
use std::fs;
use std::io::Result;
use std::process::Command;
use std::{collections::HashMap, path::Path};

use crate::initialization_typ::{
    compute_initialization_typ, override_initialization_typ, InitializationType,
};
use common::templates::*;
use common::verify_scope::*;

fn compile_variable_intro(
    handlebars: &mut Handlebars,
    intro: &VariableIntro,
    vars_to_initialization_typ: &mut HashMap<Variable, InitializationType>,
    inside_definition_filter: bool,
    inside_only_via: bool,
    initialization_typ_override: Option<InitializationType>,
) -> (String, String) {
    let mut map: HashMap<&str, String> = HashMap::new();
    map.insert("var", intro.variable.clone());

    let initialization_typ = if initialization_typ_override.is_some() {
        initialization_typ_override
    } else {
        compute_initialization_typ(&intro.intro, inside_only_via)
    };

    match &intro.intro {
        VariableIntroType::Roots | VariableIntroType::AllNodes | VariableIntroType::Variable => {}
        VariableIntroType::VariableMarked { marker, on_type: _ } => {
            map.insert("marker", marker.into());
            let Some(typ) = initialization_typ else {
                panic!("variables marked need to be initialized");
            };
            if matches!(typ, InitializationType::NodeCluster) {
                map.insert("node-cluster", "true".to_string());
            }
        }
        VariableIntroType::VariableSourceOf(type_var) => {
            map.insert("type-var", type_var.into());

            // The filter() in a definition requires an extra dereference
            if inside_definition_filter {
                map.insert("typ-definition", "true".to_string());
            }
        }
    };

    if let Some(typ) = initialization_typ {
        vars_to_initialization_typ.insert(intro.variable.clone(), typ);
    }

    (
        intro.variable.clone(),
        render_template(handlebars, &map, intro.into()),
    )
}

fn compile_relation(
    handlebars: &mut Handlebars,
    relation: &Relation,
    vars_to_initialization_typ: &HashMap<Variable, InitializationType>,
) -> String {
    let mut map: HashMap<&str, String> = HashMap::new();
    match relation {
        Relation::Binary { left, right, .. } => {
            map.insert("src", left.into());
            map.insert("sink", right.into());
            if let Some(typ) = vars_to_initialization_typ.get(right) {
                if matches!(typ, InitializationType::NodeCluster) {
                    map.insert("node-cluster", "true".to_string());
                }
            }
        }
        Relation::Negation(inner) => {
            let value = compile_relation(handlebars, inner, vars_to_initialization_typ);
            map.insert("value", value);
        }
        Relation::IsMarked(var, marker) => {
            map.insert("src", var.into());
            map.insert("marker", marker.into());
        }
    }
    render_template(handlebars, &map, relation.into())
}

fn compile_only_via(
    handlebars: &mut Handlebars,
    node: &ASTNode,
    vars_to_initialization_typ: &mut HashMap<Variable, InitializationType>,
) -> String {
    let ASTNode::OnlyVia(src_intro, sink_intro, checkpoint_intro) = node else {
        panic!("Called render_only_via on the wrong kind of node");
    };
    let mut map: HashMap<&str, Vec<String>> = HashMap::new();

    fn render_only_via_intro(
        handlebars: &mut Handlebars,
        intro: &VariableIntro,
        vars_to_initialization_typ: &mut HashMap<Variable, InitializationType>,
    ) -> (Variable, String) {
        let mut regular_template_map: HashMap<&str, String> = HashMap::new();
        let (var, intro) = compile_variable_intro(
            handlebars,
            intro,
            vars_to_initialization_typ,
            false,
            true,
            None,
        );
        regular_template_map.insert("var", var.clone());
        // If the intro refers to a previously defined variable, `intro` will be an empty string, which the template will detect so it doesn't render anything
        regular_template_map.insert("intro", intro);
        (
            var,
            render_template(handlebars, &regular_template_map, Template::OnlyViaIntro),
        )
    }

    // Prepare the sink or checkpoint intros, which may need to handle multiple collections
    fn prepare_multiple_intros<'a>(
        handlebars: &mut Handlebars,
        joined_intros: &(Option<Operator>, Vec<VariableIntro>),
        map: &mut HashMap<&'a str, Vec<String>>,
        vars_to_initialization_typ: &mut HashMap<Variable, InitializationType>,
        intro_key: &'a str,
        name_key: &'a str,
        operator_key: &'a str,
    ) {
        let (operator, intros) = joined_intros;
        if let Some(Operator::Or) = operator {
            map.insert(operator_key, vec![String::from("true")]);
        }
        let mut compiled_intros: Vec<String> = vec![];
        let mut vars: Vec<String> = vec![];
        for intro in intros {
            let (var, intro) = render_only_via_intro(handlebars, intro, vars_to_initialization_typ);
            compiled_intros.push(intro);
            vars.push(var);
        }
        map.insert(intro_key, compiled_intros);
        map.insert(name_key, vars);
    }

    let (src, src_intro) = render_only_via_intro(handlebars, src_intro, vars_to_initialization_typ);
    map.insert("src", vec![src]);
    map.insert("src-intro", vec![src_intro]);
    prepare_multiple_intros(
        handlebars,
        sink_intro,
        &mut map,
        vars_to_initialization_typ,
        "sink-intros",
        "sink-names",
        "sink-or",
    );
    prepare_multiple_intros(
        handlebars,
        checkpoint_intro,
        &mut map,
        vars_to_initialization_typ,
        "checkpoint-intros",
        "checkpoint-names",
        "checkpoint-or",
    );

    render_only_via_template(handlebars, &map)
}

// for joined nodes, we don't know how many expressions we're and/oring together in the whole policy,
// so use the counter to give each variable a unique name -- see and/or templates for more context
fn compile_ast_node(
    handlebars: &mut Handlebars,
    node: &ASTNode,
    counter: &mut u32,
    vars_to_initialization_typ: &mut HashMap<Variable, InitializationType>,
    inside_definition_filter: bool,
) -> String {
    let mut map: HashMap<&str, String> = HashMap::new();
    match node {
        ASTNode::Relation(relation) => {
            compile_relation(handlebars, relation, vars_to_initialization_typ)
        }
        ASTNode::OnlyVia(..) => compile_only_via(handlebars, node, vars_to_initialization_typ),
        ASTNode::JoinedNodes(obligation) => {
            let src_res = compile_ast_node(
                handlebars,
                &obligation.src,
                counter,
                vars_to_initialization_typ,
                inside_definition_filter,
            );
            map.insert("src", src_res);
            let sink_res = compile_ast_node(
                handlebars,
                &obligation.sink,
                counter,
                vars_to_initialization_typ,
                inside_definition_filter,
            );
            map.insert("sink", sink_res);
            map.insert("counter", counter.to_string());
            *counter += 1;
            render_template(handlebars, &map, node.into())
        }
        ASTNode::Clause(clause) => {
            let (variable_to_remove, variable_intro) = match &clause.intro {
                ClauseIntro::ForEach(intro) | ClauseIntro::ThereIs(intro) => {
                    // Only remove a variable when the clause goes out of scope if it's one we're introducing here
                    let already_present = vars_to_initialization_typ.get(&intro.variable).is_some();
                    let initialization_typ_override =
                        override_initialization_typ(intro, &clause.body);
                    let (variable, variable_intro) = compile_variable_intro(
                        handlebars,
                        intro,
                        vars_to_initialization_typ,
                        inside_definition_filter,
                        false,
                        initialization_typ_override,
                    );

                    let Some(typ) = vars_to_initialization_typ.get(&variable) else {
                        panic!("variable has been initialized but not in map")
                    };
                    if matches!(typ, InitializationType::NodeCluster) {
                        map.insert("node-cluster", "true".to_string());
                    }
                    if already_present {
                        map.insert("refers-to-definition", "true".to_string());
                    }

                    map.insert("var", variable.clone());

                    let variable_to_remove = if already_present {
                        None
                    } else {
                        Some(variable)
                    };
                    (variable_to_remove, variable_intro)
                }
                ClauseIntro::Conditional(relation) => (
                    None,
                    compile_relation(handlebars, relation, vars_to_initialization_typ),
                ),
            };

            map.insert("intro", variable_intro);
            let body = compile_ast_node(
                handlebars,
                &clause.body,
                counter,
                vars_to_initialization_typ,
                inside_definition_filter,
            );

            // variable going out of scope
            if let Some(variable) = variable_to_remove {
                vars_to_initialization_typ.remove_entry(&variable);
            }

            map.insert("body", body);
            render_template(handlebars, &map, node.into())
        }
        ASTNode::FusedClause(fused_clause) => {
            let outer_var = &fused_clause.outer_var;
            let inner_var = &fused_clause.filter.variable;

            map.insert("outer_var", outer_var.clone());
            map.insert("inner_var", inner_var.clone());
            let VariableIntroType::VariableMarked {
                ref marker,
                on_type: _,
            } = fused_clause.filter.intro
            else {
                unreachable!()
            };
            map.insert("marker", marker.clone());
            map.insert("conditional", fused_clause.is_conditional.to_string());

            // Only remove a variable when the clause goes out of scope if it's one we're introducing here
            // Fused clause outer variables should have been initialized in the intro
            assert!(vars_to_initialization_typ
                .get(&fused_clause.outer_var)
                .is_some());

            // Inner clauses introduce two variables; one named {{outer_var}}_{{marker}}
            // and one named {{inner_var}} (see templates/fused-clauses) for details.
            let outer_var_marker = format!("{}_{}", &outer_var, marker);
            vars_to_initialization_typ.insert(
                outer_var_marker.clone(),
                InitializationType::GlobalNodesIterator,
            );
            vars_to_initialization_typ.insert(inner_var.clone(), InitializationType::NodeCluster);

            if let Some(rest) = &fused_clause.rest {
                let rest = compile_ast_node(
                    handlebars,
                    rest,
                    counter,
                    vars_to_initialization_typ,
                    inside_definition_filter,
                );
                map.insert("rest", rest);
            }

            vars_to_initialization_typ.remove_entry(&outer_var_marker);
            vars_to_initialization_typ.remove_entry(inner_var);

            render_template(handlebars, &map, node.into())
        }
    }
}

fn compile_definition(
    handlebars: &mut Handlebars,
    definition: &Definition,
    policy_scope: &PolicyScope,
    policy_body: &ASTNode,
    vars_to_initialization_typ: &mut HashMap<Variable, InitializationType>,
) -> String {
    let mut map: HashMap<&str, String> = HashMap::new();

    let mut initialization_typ_override = None;
    if let Some(origin) = definition.lifted_from {
        if matches!(origin, OgClauseIntroType::ThereIs)
            || matches!(origin, OgClauseIntroType::ForEach)
        {
            initialization_typ_override =
                override_initialization_typ(&definition.declaration, policy_body);
        }
    }

    let (_, variable_intro) = compile_variable_intro(
        handlebars,
        &VariableIntro {
            variable: definition.variable.clone(),
            intro: definition.declaration.intro.clone(),
        },
        vars_to_initialization_typ,
        false,
        false,
        initialization_typ_override,
    );

    let Some(typ) = vars_to_initialization_typ.get(&definition.variable) else {
        panic!("compile_variable_intro did not initialize the defintion variable in the map")
    };
    if matches!(typ, InitializationType::NodeCluster) {
        map.insert("node-cluster", "true".to_string());
    }

    let inner_var = definition.declaration.variable.clone();
    map.insert("inner_var", inner_var.clone());
    map.insert("var", definition.variable.clone());
    map.insert("intro", variable_intro);
    let mut counter = 0;
    if let Some(filter) = &definition.filter {
        // just need to insert it so that we don't try to take a reference to it
        let already_present = vars_to_initialization_typ
            .insert(inner_var.clone(), InitializationType::GlobalNodesIterator)
            .is_some();
        let filter = compile_ast_node(
            handlebars,
            filter,
            &mut counter,
            vars_to_initialization_typ,
            true,
        );
        map.insert("filter", filter);

        // If the inner var wasn't already in the map, then remove it.
        // If it was already in the map, it had to refer to a previous definition (I think?)
        if !already_present {
            vars_to_initialization_typ.remove_entry(&inner_var);
        }
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
    policy_body: &ASTNode,
    vars_to_initialization_typ: &mut HashMap<Variable, InitializationType>,
) -> String {
    // Definitions use their own environment so that each definition only knows about the definition(s) above it.
    // This is important if the filter in one definition uses the same variable name as the name of a later definition;
    // the filter variable shouldn't reference the later definition.
    let mut env = Environment::new();
    let mut results = vec![];

    // should be compiling everything in the same order it was declared
    // so that the env doesn't reference stuff that's declared later
    for definition in definitions {
        let result = compile_definition(
            handlebars,
            definition,
            policy_scope,
            policy_body,
            vars_to_initialization_typ,
        );
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
    let mut vars_to_initialization_typ = HashMap::new();
    let (global_definitions, ctrler_definitions): (Vec<_>, Vec<_>) = policy
        .definitions
        .into_iter()
        .partition(|def| matches!(def.scope, DefinitionScope::Everywhere));
    let compiled_global_definitions = compile_definitions(
        &mut handlebars,
        &global_definitions,
        &policy.scope,
        &policy.body,
        &mut vars_to_initialization_typ,
    );
    let compiled_ctrler_definitions = compile_definitions(
        &mut handlebars,
        &ctrler_definitions,
        &policy.scope,
        &policy.body,
        &mut vars_to_initialization_typ,
    );
    map.insert("global-definitions", compiled_global_definitions);
    map.insert("definitions", compiled_ctrler_definitions);

    let mut counter = 0;

    let compiled_body = compile_ast_node(
        &mut handlebars,
        &policy.body,
        &mut counter,
        &mut vars_to_initialization_typ,
        false,
    );
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
