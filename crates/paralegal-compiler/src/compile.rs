use crate::common::{
    ast::*,
    vis::{self, VisitMut},
    Policy, PolicyScope,
};
use handlebars::Handlebars;
use std::fs;
use std::io::Result;
use std::process::Command;
use std::{collections::HashMap, path::Path};

use crate::common::templates::*;
use crate::common::verify_scope::*;
use crate::initialization_typ::{
    compute_initialization_typ, compute_lifted_def_initialization_typ, InitializationType,
};

fn compile_variable_intro(
    handlebars: &mut Handlebars,
    intro: &VariableIntro,
    vars_to_initialization_typ: &mut HashMap<Variable, InitializationType>,
    inside_definition_filter: bool,
    initialization_typ: Option<InitializationType>,
) -> (String, String) {
    let mut map: HashMap<&str, String> = HashMap::new();
    map.insert("var", intro.variable.clone());

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
    vars_to_clause_typ: &HashMap<Variable, OgClauseIntroType>,
    map: &mut HashMap<&str, String>,
) -> String {
    let mut compile_inner_relation = |relation: &Relation, inside_negation: bool| -> String {
        match relation {
            Relation::Binary { left, right, .. } => {
                map.insert("src", left.into());
                map.insert("sink", right.into());
                if let Some(typ) = vars_to_initialization_typ.get(right) {
                    if matches!(typ, InitializationType::NodeCluster) {
                        map.insert("sink-node-cluster", "true".to_string());
                    }
                } else {
                    panic!(
                        "Tried to compile a relation whose sink is not in vars_to_initialization_typ"
                    );
                }
                if let Some(typ) = vars_to_clause_typ.get(right) {
                    if inside_negation ^ matches!(typ, OgClauseIntroType::ForEach) {
                        map.insert("sink-all-method", "true".to_string());
                    }
                } else {
                    panic!("Tried to compile a relation whose sink is not in vars_to_clause_typ");
                }
            }
            Relation::Negation(_) => {
                unreachable!("called compile_inner_relation on a negation")
            }
            Relation::IsMarked(var, marker) => {
                map.insert("src", var.into());
                map.insert("marker", marker.into());
            }
        }
        render_template(handlebars, map, relation.into())
    };

    match relation {
        Relation::Binary { .. } | Relation::IsMarked { .. } => {
            compile_inner_relation(relation, false)
        }
        Relation::Negation(inner) => {
            let value = compile_inner_relation(inner, true);
            map.insert("value", value);
            render_template(handlebars, map, relation.into())
        }
    }
}

fn compile_only_via(
    handlebars: &mut Handlebars,
    node: &ASTNode,
    vars_to_initialization_typ: &mut HashMap<Variable, InitializationType>,
) -> String {
    let ASTNodeType::OnlyVia(src_intro, sink_intro, checkpoint_intro) = &node.ty else {
        panic!("Called render_only_via on the wrong kind of node");
    };
    let mut map: HashMap<&str, Vec<String>> = HashMap::new();
    map.insert("clause_num", vec![node.clause_num.clone()]);
    map.insert("span", vec![node.span.clone()]);

    fn render_only_via_intro(
        handlebars: &mut Handlebars,
        intro: &VariableIntro,
        vars_to_initialization_typ: &mut HashMap<Variable, InitializationType>,
    ) -> (Variable, String) {
        let mut regular_template_map: HashMap<&str, String> = HashMap::new();
        // Rationale: the choice of iterator vs. NodeCluster is irrelevant for a variable marked introduced in an only via, since we're just going to collect it and run contains() anyway.
        let initialization_typ = if matches!(intro.intro, VariableIntroType::Variable) {
            None
        } else {
            Some(InitializationType::GlobalNodesIterator)
        };
        let (var, intro) = compile_variable_intro(
            handlebars,
            intro,
            vars_to_initialization_typ,
            false,
            initialization_typ,
        );
        regular_template_map.insert("var", var.clone());
        // If the intro refers to a previously defined variable, `intro` will be an empty string, which the template will detect so it doesn't render anything
        regular_template_map.insert("intro", intro);

        if matches!(
            vars_to_initialization_typ.get(&var),
            Some(InitializationType::NodeCluster)
        ) {
            regular_template_map.insert("node-cluster", "true".to_string());
        }
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
    vars_to_clause_typ: &mut HashMap<Variable, OgClauseIntroType>,
    inside_definition_filter: bool,
) -> String {
    let mut map: HashMap<&str, String> = HashMap::new();
    map.insert("clause_num", node.clause_num.clone());
    map.insert("span", node.span.clone());
    match &node.ty {
        ASTNodeType::Relation(relation) => compile_relation(
            handlebars,
            relation,
            vars_to_initialization_typ,
            vars_to_clause_typ,
            &mut map,
        ),
        ASTNodeType::OnlyVia(..) => compile_only_via(handlebars, node, vars_to_initialization_typ),
        ASTNodeType::JoinedNodes(obligation) => {
            let src_res = compile_ast_node(
                handlebars,
                &obligation.src,
                counter,
                vars_to_initialization_typ,
                vars_to_clause_typ,
                inside_definition_filter,
            );
            map.insert("src", src_res);
            let sink_res = compile_ast_node(
                handlebars,
                &obligation.sink,
                counter,
                vars_to_initialization_typ,
                vars_to_clause_typ,
                inside_definition_filter,
            );
            map.insert("sink", sink_res);
            map.insert("counter", counter.to_string());
            *counter += 1;
            render_template(handlebars, &map, node.into())
        }
        ASTNodeType::Clause(clause) => {
            let (variable_to_remove, variable_intro) = match &clause.intro {
                ClauseIntro::ForEach(intro) | ClauseIntro::ThereIs(intro) => {
                    // Only remove a variable when the clause goes out of scope if it's one we're introducing here
                    let already_present = vars_to_initialization_typ.get(&intro.variable).is_some();
                    let initilization_typ =
                        compute_initialization_typ(&clause.body, (&clause.intro).into(), intro);
                    let (variable, variable_intro) = compile_variable_intro(
                        handlebars,
                        intro,
                        vars_to_initialization_typ,
                        inside_definition_filter,
                        initilization_typ,
                    );

                    let Some(typ) = vars_to_initialization_typ.get(&variable) else {
                        panic!("variable has been initialized but not in map")
                    };
                    if matches!(typ, InitializationType::NodeCluster) {
                        map.insert("node-cluster", "true".to_string());
                    }
                    if already_present {
                        map.insert("refers-to-definition", "true".to_string());
                    } else {
                        vars_to_clause_typ.insert(variable.clone(), (&clause.intro).into());
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
                    compile_relation(
                        handlebars,
                        relation,
                        vars_to_initialization_typ,
                        vars_to_clause_typ,
                        &mut map,
                    ),
                ),
            };

            map.insert("intro", variable_intro);

            let body = compile_ast_node(
                handlebars,
                &clause.body,
                counter,
                vars_to_initialization_typ,
                vars_to_clause_typ,
                inside_definition_filter,
            );

            // variable going out of scope
            if let Some(variable) = variable_to_remove {
                vars_to_initialization_typ.remove_entry(&variable);
                vars_to_clause_typ.remove_entry(&variable);
            }

            map.insert("body", body);
            render_template(handlebars, &map, node.into())
        }
    }
}

fn compile_definition(
    handlebars: &mut Handlebars,
    definition: &Definition,
    policy_scope: &PolicyScope,
    initialization_typ: InitializationType,
    vars_to_initialization_typ: &mut HashMap<Variable, InitializationType>,
    vars_to_clause_typ: &mut HashMap<Variable, OgClauseIntroType>,
) -> String {
    let mut map: HashMap<&str, String> = HashMap::new();

    let (_, variable_intro) = compile_variable_intro(
        handlebars,
        &VariableIntro {
            variable: definition.variable.clone(),
            intro: definition.declaration.intro.clone(),
        },
        vars_to_initialization_typ,
        false,
        Some(initialization_typ),
    );

    let Some(typ) = vars_to_initialization_typ.get(&definition.variable) else {
        panic!("compile_variable_intro did not initialize the defintion variable in the map")
    };
    if matches!(typ, InitializationType::NodeCluster) {
        map.insert("node-cluster", "true".to_string());
    }

    let inner_var = &definition.declaration.variable;
    map.insert("inner_var", inner_var.clone());
    map.insert("var", definition.variable.clone());
    map.insert("intro", variable_intro);
    let mut counter = 0;
    if let Some(filter) = &definition.filter {
        // Relations in filters need access to the inner variable to compile
        if let Some(typ) = definition.lifted_from {
            vars_to_clause_typ.insert(inner_var.clone(), typ);
        } else {
            // If it's not a lifted definition, then it must be all objects that satisfy the definition
            // since that's the only kind that parses.
            // The declaration's variable is the one that the relations are in terms of.
            vars_to_clause_typ.insert(inner_var.clone(), OgClauseIntroType::ForEach);
        }

        // just need to insert it so that we don't try to take a reference to it
        let already_present = vars_to_initialization_typ
            .insert(inner_var.clone(), InitializationType::GlobalNodesIterator)
            .is_some();
        let filter = compile_ast_node(
            handlebars,
            filter,
            &mut counter,
            vars_to_initialization_typ,
            vars_to_clause_typ,
            true,
        );
        map.insert("filter", filter);

        // If the inner var wasn't already in the map, then remove it.
        // If it was already in the map, it had to refer to a previous definition
        if !already_present {
            vars_to_initialization_typ.remove_entry(inner_var);
        }
        vars_to_clause_typ.remove_entry(inner_var);
    }

    // Now that the definition is there, the outer variable should be referenceable
    if let Some(typ) = definition.lifted_from {
        vars_to_clause_typ.insert(definition.variable.clone(), typ);
    } else {
        vars_to_clause_typ.insert(definition.variable.clone(), OgClauseIntroType::ForEach);
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
    policy: &Policy,
    vars_to_initialization_typ: &mut HashMap<Variable, InitializationType>,
    vars_to_clause_typ: &mut HashMap<Variable, OgClauseIntroType>,
) -> String {
    // Definitions use their own environment so that each definition only knows about the definition(s) above it.
    // This is important if the filter in one definition uses the same variable name as the name of a later definition;
    // the filter variable shouldn't reference the later definition.
    let mut env = Environment::new();
    let mut results = vec![];

    // should be compiling everything in the same order it was declared
    // so that the env doesn't reference stuff that's declared later

    for def_idx in 0..definitions.len() {
        let definition = &definitions[def_idx];
        let mut initialization_typ = InitializationType::NodeCluster;

        if definition.lifted_from.is_some() {
            // the problem here is that we lifted this from some clause, so we can't look at the whole policy body.
            // we should only look at the clause that we lifted it from.
            // so need to find the clause that introduced it (we know there's only one, since we don't lift unless that's the case)
            // and then only search the body from there.
            // we don't need to look at the other definitions, since definitions can only refer to other definitions, not compiler-lifted ones
            initialization_typ = compute_lifted_def_initialization_typ(definition, &policy.body);
        } else {
            let clause_intro_typ = if let Some(clause_intro_typ) = definition.lifted_from {
                clause_intro_typ
            } else {
                OgClauseIntroType::ForEach
            };
            let var_intro = VariableIntro {
                variable: definition.variable.clone(),
                intro: definition.declaration.intro.clone(),
            };
            for later_def in definitions.iter().skip(def_idx + 1) {
                // Evaluate the appropriate declaration of the outer definition
                // by examining how the latter one's filter body (the latter one may reference it).
                if let Some(filter) = later_def.filter.as_ref() {
                    let typ = compute_initialization_typ(
                        filter,
                        clause_intro_typ,
                        &var_intro,
                    )
                .unwrap_or_else(|| {
                    panic!("computer_initialization_typ returned None for a definition declaration")
                });
                    // if we find that we should override, do it.
                    // we need to check explicitly like this to avoid overwriting previous overrides.
                    if matches!(typ, InitializationType::GlobalNodesIterator) {
                        initialization_typ = typ;
                    }
                }
            }
            // then examine how the policy uses it
            let typ = compute_initialization_typ(&policy.body, clause_intro_typ, &var_intro)
                .unwrap_or_else(|| {
                    panic!("computer_initialization_typ returned None for a definition declaration")
                });
            if matches!(typ, InitializationType::GlobalNodesIterator) {
                initialization_typ = typ;
            }
        }

        let result = compile_definition(
            handlebars,
            definition,
            &policy.scope,
            initialization_typ,
            vars_to_initialization_typ,
            vars_to_clause_typ,
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

pub fn compile(mut policy: Policy, policy_name: &str, out: &Path, create_bin: bool) -> Result<()> {
    let mut propagator = ClauseNumPropagator {
        current: String::new(),
    };
    propagator.visit_ast_node_mut(&mut policy.body);

    let mut handlebars = Handlebars::new();
    handlebars.set_strict_mode(true);
    register_templates(&mut handlebars);

    // compile definitions & policy
    let mut map: HashMap<&str, String> = HashMap::new();
    // Map each variable to whether it should be initialized with a NodeCluster or Iterator<Item = GlobalNode> in the policy
    let mut vars_to_initialization_typ = HashMap::new();
    // Map each variable to its clause intro type in the policy
    let mut vars_to_clause_typ = HashMap::new();
    let (global_definitions, ctrler_definitions): (Vec<_>, Vec<_>) = policy
        .definitions
        .clone()
        .into_iter()
        .partition(|def| matches!(def.scope, DefinitionScope::Everywhere));
    let compiled_global_definitions = compile_definitions(
        &mut handlebars,
        &global_definitions,
        &policy,
        &mut vars_to_initialization_typ,
        &mut vars_to_clause_typ,
    );
    let compiled_ctrler_definitions = compile_definitions(
        &mut handlebars,
        &ctrler_definitions,
        &policy,
        &mut vars_to_initialization_typ,
        &mut vars_to_clause_typ,
    );
    map.insert("global-definitions", compiled_global_definitions);
    map.insert("definitions", compiled_ctrler_definitions);

    let mut counter = 0;

    let compiled_body = compile_ast_node(
        &mut handlebars,
        &policy.body,
        &mut counter,
        &mut vars_to_initialization_typ,
        &mut vars_to_clause_typ,
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

struct ClauseNumPropagator {
    current: String,
}

impl VisitMut<'_> for ClauseNumPropagator {
    fn visit_ast_node_mut(&mut self, node: &mut ASTNode) {
        let old = if !node.clause_num.is_empty() {
            let new = format!(
                "{}{}{}",
                self.current,
                if self.current.is_empty() { "" } else { "." },
                node.clause_num
            );
            Some(std::mem::replace(&mut self.current, new))
        } else {
            None
        };
        vis::super_visit_ast_node_mut(self, node);
        if let Some(old) = old {
            self.current = old;
        }
    }

    fn visit_clause_num_mut(&mut self, clause_num: &mut String) {
        if !clause_num.is_empty() && !self.current.is_empty() {
            *clause_num = self.current.clone();
        }
    }
}
