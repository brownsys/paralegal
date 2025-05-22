use std::collections::HashSet;

use common::{ast::*, count_references_to_variable};

// How a variable is being initialized in the compiled policy
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum InitializationType {
    NodeCluster,
    GlobalNodesIterator,
}

/// Compute the appropriate initialization type for a variable intro.
pub fn compute_initialization_typ(
    body: &ASTNode,
    clause_intro_typ: OgClauseIntroType,
    var_intro: &VariableIntro,
) -> Option<InitializationType> {
    match &var_intro.intro {
        VariableIntroType::Roots
        | VariableIntroType::AllNodes
        | VariableIntroType::VariableSourceOf(..) => Some(InitializationType::GlobalNodesIterator),
        // Already initialized
        VariableIntroType::Variable => None,
        VariableIntroType::VariableMarked { marker: _, on_type } => {
            // Variable source of doesn't play well with node clusters, so don't use them for types
            if *on_type {
                return Some(InitializationType::GlobalNodesIterator);
            }

            let mut initialization_typ = InitializationType::NodeCluster;

            match clause_intro_typ {
                OgClauseIntroType::ForEach => {
                    for_each_initialization_typ(
                        &var_intro.variable,
                        body,
                        &None,
                        &mut initialization_typ,
                    );
                }
                OgClauseIntroType::ThereIs => {
                    there_is_initialization_typ(&var_intro.variable, body, &mut initialization_typ);
                }
                OgClauseIntroType::Conditional => todo!("i think this is unreachable???"),
            }

            Some(initialization_typ)
        }
    }
}

/// Determine how a lifted definition should be initialized.
pub fn compute_lifted_def_initialization_typ(
    definition: &Definition,
    body: &ASTNode,
) -> InitializationType {
    fn find_matching_clause(definition: &Definition, body: &ASTNode) -> Option<Clause> {
        match body {
            ASTNode::Clause(clause) => {
                match &clause.intro {
                    ClauseIntro::ForEach(intro) | ClauseIntro::ThereIs(intro) => {
                        if intro.variable == definition.variable {
                            return Some(*clause.clone());
                        }
                    }
                    ClauseIntro::Conditional(_) => {}
                }
                find_matching_clause(definition, &clause.body)
            }
            ASTNode::JoinedNodes(obligation) => find_matching_clause(definition, &obligation.src)
                .or_else(|| find_matching_clause(definition, &obligation.sink)),
            _ => None,
        }
    }
    let clause = find_matching_clause(definition, body).unwrap_or_else(|| {
        panic!(
            "Should have found clause that introduced the lifted definition {:?}",
            definition
        )
    });
    compute_initialization_typ(
        &clause.body,
        (&clause.intro).into(),
        &definition.declaration,
    )
    .unwrap_or_else(|| panic!("Lifted definitions always need to be initialized"))
}

// if it's a for each variable, then it can be a node cluster if:
//     - it's not a type
//     - not referenced in an associated call site relation
//     - not *first* introduced in an only via; if it's referenced earlier and then used in an only via later,
//       that should be ok bc any short circuting would have already happened.
//     - all of the references are sinks
//     - all of the references are srcs in a binary negation relation (except is_marked),
//       because that can be rewritten as "there does not exist"
//     - if it's in a conditional premise, then only if it's never referenced again after the premise.
fn for_each_initialization_typ(
    variable: &Variable,
    body: &ASTNode,
    conditional_premise_vars: &Option<&mut HashSet<Variable>>,
    initialization_typ: &mut InitializationType,
) {
    match body {
        ASTNode::Relation(relation) => match relation {
            Relation::Binary { left, right, typ } => {
                if variable == left
                    || (variable == right
                        && conditional_premise_vars
                            .as_ref()
                            .is_some_and(|cvp| cvp.contains(variable)))
                    || matches!(typ, Binop::AssociatedCallSite)
                {
                    *initialization_typ = InitializationType::GlobalNodesIterator;
                }
            }
            Relation::Negation(relation) => match *relation.clone() {
                Relation::Binary { left, right, typ } => {
                    if *variable == right
                        || (*variable == left
                            && conditional_premise_vars
                                .as_ref()
                                .is_some_and(|cvp| cvp.contains(variable)))
                        || matches!(typ, Binop::AssociatedCallSite)
                    {
                        *initialization_typ = InitializationType::GlobalNodesIterator;
                    }
                }
                Relation::Negation(_) => unreachable!("double negation doesn't parse"),
                Relation::IsMarked(var, _) => {
                    if *variable == var {
                        *initialization_typ = InitializationType::GlobalNodesIterator;
                    }
                }
            },
            Relation::IsMarked(..) => {}
        },
        ASTNode::Clause(clause) => match clause.intro.clone() {
            ClauseIntro::ForEach(..) | ClauseIntro::ThereIs(..) => {
                for_each_initialization_typ(
                    variable,
                    &clause.body,
                    conditional_premise_vars,
                    initialization_typ,
                );
            }
            ClauseIntro::Conditional(relation) => {
                let mut conditional_premise_vars: HashSet<Variable> = HashSet::new();
                match relation {
                    Relation::Binary { left, right, .. } => {
                        conditional_premise_vars.insert(left);
                        conditional_premise_vars.insert(right);
                    }
                    Relation::Negation(relation) => match *relation {
                        Relation::Binary { left, right, .. } => {
                            conditional_premise_vars.insert(left);
                            conditional_premise_vars.insert(right);
                        }
                        Relation::Negation(_) => unreachable!("double negation doesn't parse"),
                        Relation::IsMarked(var, _) => {
                            conditional_premise_vars.insert(var);
                        }
                    },
                    Relation::IsMarked(var, _) => {
                        conditional_premise_vars.insert(var);
                    }
                };
                for_each_initialization_typ(
                    variable,
                    &clause.body,
                    &Some(&mut conditional_premise_vars),
                    initialization_typ,
                );
            }
        },
        ASTNode::JoinedNodes(obligation) => {
            for_each_initialization_typ(
                variable,
                &obligation.src,
                conditional_premise_vars,
                initialization_typ,
            );
            for_each_initialization_typ(
                variable,
                &obligation.sink,
                conditional_premise_vars,
                initialization_typ,
            );
        }
        ASTNode::OnlyVia(..) => {
            // render_only_via doesn't call this function, so if we reach this point, we're evaluating a definition declaration that gets referenced in an only via.
            // Since the templates implement contains() for NodeClusters that just collect the nodes and iterate over them one at a time anyway,
            // there's no need to override here; it doesn't matter which typ we use.
        }
    }
}

// If it's a there is variable, then it can be a nodecluster if it gets referenced once in the clause
// as long as it's not used an associated call site relation, which need to reason about the same object across two graph queries
fn there_is_initialization_typ(
    variable: &Variable,
    body: &ASTNode,
    initialization_typ: &mut InitializationType,
) {
    // Associated call sites can't use node clusters
    fn var_in_associated_call_site_relation(variable: &Variable, body: &ASTNode) -> bool {
        match body {
            ASTNode::Relation(relation) => match relation {
                Relation::Binary { left, right, typ } => {
                    (variable == left || variable == right)
                        && matches!(typ, Binop::AssociatedCallSite)
                }
                Relation::Negation(relation) => match &**relation {
                    Relation::Binary { left, right, typ } => {
                        (variable == left || variable == right)
                            && matches!(typ, Binop::AssociatedCallSite)
                    }
                    Relation::Negation(_) => unreachable!("double negation doesn't parse"),
                    Relation::IsMarked(..) => false,
                },
                Relation::IsMarked(..) => false,
            },
            ASTNode::Clause(clause) => var_in_associated_call_site_relation(variable, &clause.body),
            ASTNode::OnlyVia(..) => false,
            ASTNode::JoinedNodes(obligation) => {
                var_in_associated_call_site_relation(variable, &obligation.src)
                    || var_in_associated_call_site_relation(variable, &obligation.sink)
            }
        }
    }

    let mut count = 0;
    count_references_to_variable(variable, body, &mut count);
    if count > 1 || var_in_associated_call_site_relation(variable, body) {
        *initialization_typ = InitializationType::GlobalNodesIterator;
    }
}
