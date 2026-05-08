use crate::common::{ast::*, Policy};

/// Traverse the policy body and lift variable declarations to be definitions where possible.
/// This lets us avoid repeated graph searches for the same variables.
type LiftedIntros = Vec<(VariableIntro, OgClauseIntroType)>;

/// Traverse the policy body and lift variable declarations to be definitions where possible.
/// This lets us avoid repeated graph searches for the same variables.
fn lift_definitions(policy: &mut Policy) {
    // This needs to be a vector, rather than a HashMap, to preserve the order that the policy declares variables.
    let mut intros: Vec<(&Variable, LiftedIntros)> = Vec::new();
    let mut queue: Vec<&ASTNode> = vec![];
    queue.push(&policy.body);

    fn add_intro_to_vec<'a>(
        intros: &mut Vec<(&'a Variable, LiftedIntros)>,
        var_intro: &'a VariableIntro,
        clause_intro: &'a ClauseIntro,
    ) {
        let var = &var_intro.variable;
        if let Some((_, intros_list)) = intros.iter_mut().find(|(v, _)| **v == *var) {
            intros_list.push((var_intro.clone(), clause_intro.into()));
        } else {
            intros.push((var, vec![(var_intro.clone(), clause_intro.into())]));
        }
    }

    // Conditionals require reasoning about individual elements, so their clause intros are ineligible for lifting
    // Remove them from the vector.
    fn handle_ineligibility(relation: &Relation, intros: &mut Vec<(&Variable, LiftedIntros)>) {
        match relation {
            Relation::Binary {
                left,
                right,
                typ: _,
            } => {
                intros.retain(|(v, _)| **v != *left);
                intros.retain(|(v, _)| **v != *right);
            }
            Relation::Negation(relation) => {
                handle_ineligibility(relation, intros);
            }
            Relation::IsMarked(var, _) => {
                intros.retain(|(v, _)| **v != *var);
            }
        }
    }

    // Collect how many times each variable is introduced, mapped to its introduction
    while let Some(node) = queue.pop() {
        match &node.ty {
            ASTNodeType::Clause(clause) => {
                match &clause.intro {
                    ClauseIntro::ForEach(var_intro) | ClauseIntro::ThereIs(var_intro) => {
                        match var_intro.intro {
                            VariableIntroType::AllNodes | VariableIntroType::Roots => {
                                add_intro_to_vec(&mut intros, var_intro, &clause.intro);
                            }
                            VariableIntroType::VariableMarked { on_type, .. } if !on_type => {
                                add_intro_to_vec(&mut intros, var_intro, &clause.intro);
                            }
                            // Sources of types need to be nested; do not attempt to move them
                            // Variables by themselves refer to existing definitions, so don't attempt to redefine them
                            VariableIntroType::VariableSourceOf(_)
                            | VariableIntroType::Variable
                            | VariableIntroType::VariableMarked { .. } => {}
                        }
                    }
                    ClauseIntro::Conditional(relation) => {
                        handle_ineligibility(relation, &mut intros)
                    }
                }
                queue.push(&clause.body);
            }
            ASTNodeType::JoinedNodes(obligation) => {
                queue.push(&obligation.src);
                queue.push(&obligation.sink);
            }
            ASTNodeType::Relation(ref relation) => {
                let is_eligible = match relation {
                    Relation::Binary {
                        left: _,
                        right: _,
                        typ,
                    } => !matches!(typ, Binop::AssociatedCallSite),
                    Relation::Negation(relation) => match *relation.clone() {
                        Relation::Binary {
                            left: _,
                            right: _,
                            typ,
                        } => !matches!(typ, Binop::AssociatedCallSite),
                        Relation::Negation(_) => unreachable!("Double negation should not parse"),
                        Relation::IsMarked(..) => true,
                    },
                    Relation::IsMarked(..) => true,
                };
                if !is_eligible {
                    handle_ineligibility(relation, &mut intros);
                }
            }
            // The body of the always_happens_before() call uses contains() to check for membership,
            // which doesn't exist if we
            ASTNodeType::OnlyVia(_, _, _) => {
                return;
            }
        }
    }

    // Get all the variables that are only introduced once in the whole policy
    // We can reclassify these as definitions and initialize them once, so we don't repeat graph traversals in inner loops.
    let unique = intros
        .into_iter()
        .filter_map(|(_, vec)| {
            // If the variable is only referenced once
            // or if it's referenced multiple times, but all the referes are to AllNodes or Roots, which are idempotent
            if vec.len() == 1
                || vec.iter().all(|(intro, _)| {
                    matches!(intro.intro, VariableIntroType::AllNodes)
                        || matches!(intro.intro, VariableIntroType::Roots)
                })
            {
                Some(vec[0].clone())
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    // Create new definitions
    policy
        .definitions
        .extend(unique.iter().map(|(var_intro, clause_intro_typ)| {
            Definition {
                variable: var_intro.variable.clone(),
                scope: DefinitionScope::Ctrler,
                // this is what really matters, since the template ends up just rendering this intro since filter is None
                declaration: var_intro.clone(),
                filter: None,
                lifted_from: Some(*clause_intro_typ),
            }
        }));

    // Change variable declaration types so just reference these new definitions
    let mut queue: Vec<&mut ASTNode> = vec![];
    queue.push(&mut policy.body);

    while let Some(node) = queue.pop() {
        match &mut node.ty {
            ASTNodeType::Clause(clause) => {
                let typ = (&clause.intro).into();
                match &mut clause.intro {
                    ClauseIntro::ForEach(var_intro) | ClauseIntro::ThereIs(var_intro) => {
                        if unique.contains(&(var_intro.clone(), typ)) {
                            var_intro.intro = VariableIntroType::Variable;
                        }
                    }
                    ClauseIntro::Conditional(_) => {}
                }
                queue.push(&mut clause.body);
            }
            ASTNodeType::JoinedNodes(obligation) => {
                queue.push(&mut obligation.src);
                queue.push(&mut obligation.sink);
            }
            ASTNodeType::Relation(_) | ASTNodeType::OnlyVia(_, _, _) => {}
        }
    }
}

pub fn optimize(policy: &mut Policy) {
    lift_definitions(policy);
}
