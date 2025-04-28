use common::ast::*;

// How a variable is being initialized in the compiled policy
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum InitializationType {
    NodeCluster,
    GlobalNodesIterator,
}

/// Compute the appropriate initialization type for a variable intro.
pub fn compute_initialization_typ(
    intro_typ: &VariableIntroType,
    inside_only_via: bool,
) -> Option<InitializationType> {
    match intro_typ {
        VariableIntroType::Roots
        | VariableIntroType::AllNodes
        | VariableIntroType::VariableSourceOf(..) => Some(InitializationType::GlobalNodesIterator),
        // Already initialized
        VariableIntroType::Variable => None,
        VariableIntroType::VariableMarked { marker: _, on_type } => {
            // Variable source of doesn't play well with node clusters, so don't use them for types
            // Node cluster initializations short-circuit with a boolean upon failure, but for checkpoints,
            // we can't determine a static short-circuit value; it depends on whether source goes to a sink.
            // So just use regular iterators for those too.
            if *on_type || inside_only_via {
                Some(InitializationType::GlobalNodesIterator)
            } else {
                Some(InitializationType::NodeCluster)
            }
        }
    }
}

// Count the number of times `body` references `variable`.
fn count_references_to_variable(variable: &Variable, body: &ASTNode, count: &mut u16) {
    fn relation_count(relation: &Relation, variable: &Variable, count: &mut u16) {
        match relation {
            Relation::Binary {
                left,
                right,
                typ: _,
            } => {
                if left == variable {
                    *count += 1;
                }
                if right == variable {
                    *count += 1;
                }
            }
            Relation::IsMarked(var, _) => {
                if var == variable {
                    *count += 1;
                }
            }
            Relation::Negation(relation) => relation_count(relation, variable, count),
        }
    }

    match body {
        ASTNode::Relation(relation) => relation_count(relation, variable, count),
        ASTNode::Clause(clause) => count_references_to_variable(variable, &clause.body, count),
        ASTNode::JoinedNodes(obligation) => {
            count_references_to_variable(variable, &obligation.src, count);
            count_references_to_variable(variable, &obligation.sink, count);
        }
        ASTNode::FusedClause(clause) => {
            if clause.outer_var == *variable {
                *count += 1;
            }
            if let Some(rest) = &clause.rest {
                count_references_to_variable(variable, rest, count);
            }
        }
        ASTNode::OnlyVia(..) => unreachable!("Only via can't be inside another clause."),
    }
}

pub fn there_is_initialization_typ(
    intro: &VariableIntro,
    body: &ASTNode,
) -> Option<InitializationType> {
    // Normally, we'd let compute_initialization_typ figure out the appropriate initialization type from the variable intro alone.
    // This is the one exception: if a ThereIs clause introduces a variable that gets referred to more than once,
    // we cannot use a NodeCluster. This is because ThereIs is meant to introduce a ~single~ object that can be referred to multiple times;
    // if we just lump it all together in a NodeCluster, we change the semantics of the policy.
    // But if it's only referred to once, it's fine to use a NodeCluster, since any single object that meets the criteria is fine;
    // we don't need to refer to that same object in multiple places.
    let mut initialization_typ_override = None;
    if let Some(typ) = compute_initialization_typ(&intro.intro, false) {
        if matches!(typ, InitializationType::NodeCluster) {
            let mut count = 0;
            count_references_to_variable(&intro.variable, body, &mut count);
            if count > 1 {
                initialization_typ_override = Some(InitializationType::GlobalNodesIterator)
            }
        }
    }
    initialization_typ_override
}
