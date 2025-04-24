use std::collections::HashMap;

use common::{ast::*, Policy};

pub fn optimize(policy: &mut Policy) {
    let mut intros: HashMap<&Variable, Vec<&VariableIntro>> = HashMap::new();
    let mut queue: Vec<&ASTNode> = vec![];
    queue.push(&policy.body);

    // Collect how many times each variable is introduced, mapped to its introduction
    while let Some(node) = queue.pop() {
        match node {
            ASTNode::Clause(clause) => {
                match &clause.intro {
                    ClauseIntro::ForEach(var_intro) | ClauseIntro::ThereIs(var_intro) => {
                        // Sources of types need to be nested; do not attempt to move them
                        if !matches!(var_intro.intro, VariableIntroType::VariableSourceOf(_)) {
                            intros
                                .entry(&var_intro.variable)
                                .and_modify(|intros| intros.push(var_intro))
                                .or_insert(vec![var_intro]);
                        }
                    }
                    ClauseIntro::Conditional(_) => {}
                }
                queue.push(&clause.body);
            }
            ASTNode::JoinedNodes(obligation) => {
                queue.push(&obligation.src);
                queue.push(&obligation.sink);
            }
            ASTNode::Relation(_) | ASTNode::OnlyVia(_, _, _) => {}
        }
    }

    // Get all the variables that are only introduced once in the whole policy
    // We can reclassify these as definitions and initialize them once, so we don't repeat graph traversals in inner loops
    let unique = intros
        .into_iter()
        .filter_map(|(_, intros)| {
            if intros.len() == 1 {
                Some(intros[0].clone())
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    // Create new definitions
    policy.definitions.extend(unique.iter().map(|var_intro| {
        Definition {
            variable: var_intro.variable.clone(),
            scope: DefinitionScope::Ctrler,
            // this is what really matters, since the template ends up just rendering this intro since filter is None
            declaration: var_intro.clone(),
            filter: None,
        }
    }));

    // Change variable declaration types so just reference these new definitions
    let mut queue: Vec<&mut ASTNode> = vec![];
    queue.push(&mut policy.body);

    while let Some(node) = queue.pop() {
        match node {
            ASTNode::Clause(clause) => {
                match &mut clause.intro {
                    ClauseIntro::ForEach(var_intro) | ClauseIntro::ThereIs(var_intro) => {
                        if unique.contains(&*var_intro) {
                            var_intro.intro = VariableIntroType::Variable;
                        }
                    }
                    ClauseIntro::Conditional(_) => {}
                }
                queue.push(&mut clause.body);
            }
            ASTNode::JoinedNodes(obligation) => {
                queue.push(&mut obligation.src);
                queue.push(&mut obligation.sink);
            }
            ASTNode::Relation(_) | ASTNode::OnlyVia(_, _, _) => {}
        }
    }
}
