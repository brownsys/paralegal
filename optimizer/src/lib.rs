use std::collections::HashMap;

use common::{ast::*, Policy};

type LiftedIntros = Vec<(VariableIntro, OgClauseIntroType)>;

/// Traverse the policy body and lift variable declarations to be definitions where possible.
/// This lets us avoid repeated graph searches for the same variables.
fn lift_definitions(
    policy: &mut Policy,
) -> Vec<(common::ast::VariableIntro, common::ast::OgClauseIntroType)> {
    let mut intros: HashMap<&Variable, LiftedIntros> = HashMap::new();
    let mut queue: Vec<&ASTNode> = vec![];
    queue.push(&policy.body);

    // Conditionals require reasoning about individual elements, so their clause intros are ineligible for lifting
    // Remove them from the hashmap.
    fn handle_conditional(relation: &Relation, intros: &mut HashMap<&Variable, LiftedIntros>) {
        match relation {
            Relation::Binary {
                left,
                right,
                typ: _,
            } => {
                intros.remove_entry(left);
                intros.remove_entry(right);
            }
            Relation::Negation(relation) => {
                handle_conditional(relation, intros);
            }
            Relation::IsMarked(var, _) => {
                intros.remove_entry(var);
            }
        }
    }

    // Collect how many times each variable is introduced, mapped to its introduction
    while let Some(node) = queue.pop() {
        match node {
            ASTNode::Clause(clause) => {
                match &clause.intro {
                    ClauseIntro::ForEach(var_intro) | ClauseIntro::ThereIs(var_intro) => {
                        match var_intro.intro {
                            VariableIntroType::AllNodes
                            | VariableIntroType::Roots
                            | VariableIntroType::VariableMarked { .. } => {
                                intros
                                    .entry(&var_intro.variable)
                                    .and_modify(|intros| {
                                        intros.push((var_intro.clone(), (&clause.intro).into()))
                                    })
                                    .or_insert(vec![(var_intro.clone(), (&clause.intro).into())]);
                            }
                            // Sources of types need to be nested; do not attempt to move them
                            // Variables by themselves refer to existing definitions, so don't attempt to redefine them
                            VariableIntroType::VariableSourceOf(_)
                            | VariableIntroType::Variable => {}
                        }
                    }
                    ClauseIntro::Conditional(relation) => handle_conditional(relation, &mut intros),
                }
                queue.push(&clause.body);
            }
            ASTNode::JoinedNodes(obligation) => {
                queue.push(&obligation.src);
                queue.push(&obligation.sink);
            }
            ASTNode::Relation(_) | ASTNode::OnlyVia(_, _, _) => {}
            ASTNode::FusedClause(_) => {
                unreachable!(
                    "
                    Encountered a fused node while peforming the lifting optimization.
                    This indicates a compiler bug; fusing must come after lifting."
                )
            }
        }
    }

    // Get all the variables that are only introduced once in the whole policy
    // We can reclassify these as definitions and initialize them once, so we don't repeat graph traversals in inner loops
    let unique = intros
        .into_iter()
        .filter_map(|(_, vec)| {
            if vec.len() == 1 {
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
                // we're using this as a
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
        match node {
            ASTNode::Clause(clause) => {
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
            ASTNode::JoinedNodes(obligation) => {
                queue.push(&mut obligation.src);
                queue.push(&mut obligation.sink);
            }
            ASTNode::Relation(_) | ASTNode::OnlyVia(_, _, _) => {}
            ASTNode::FusedClause(_) => {
                unreachable!(
                    "
                    Encountered a fused node while peforming the lifting optimization.
                    This indicates a compiler bug; fusing must come after lifting."
                )
            }
        }
    }

    unique
}

// Search for this pattern:
// 1. For A marked a:
//   A. For B marked b:
//     a. If BinaryRelation(A, B), then: ...
// and replace the inner clause with a FusedClause
// TODO: it would be nice if this could mutate the policy in-place, but I gave up after fighting with the borrow checker for awhile.
// I'm not sure it's trivial to do that since you need to save
fn fuse(original_policy: Policy) -> Policy {
    #[derive(Default, Debug)]
    struct FuseState {
        /// Have we seen two clauses introducing marked variables?
        ready_to_fuse: bool,
        /// The variable from the outer loop that we'll use in the fused clause
        outer_var: Option<String>,
    }

    impl FuseState {
        fn reset(&mut self) {
            self.ready_to_fuse = false;
            self.outer_var = None;
        }

        fn update_vars(&mut self, new_var: String) {
            match &self.outer_var {
                Some(_) => self.ready_to_fuse = true,
                None => self.outer_var = Some(new_var),
            }
        }

        fn try_create_fused_clause(
            &self,
            relation: &Relation,
            var_intro: &VariableIntro,
            rest: Option<ASTNode>,
            is_conditional: bool,
        ) -> Option<ASTNode> {
            if !self.ready_to_fuse {
                return None;
            }

            let outer_var = self.outer_var.as_ref()?;
            let (pos, binop) = get_binop_and_position(relation, outer_var)?;

            Some(ASTNode::FusedClause(Box::new(FusedClause {
                outer_var: outer_var.clone(),
                binop,
                pos,
                filter: var_intro.clone(),
                rest,
                is_conditional,
            })))
        }
    }

    // If this relation is eligible for fusing, return the appropriate postion and binop.
    fn get_binop_and_position(relation: &Relation, outer_var: &str) -> Option<(Position, Binop)> {
        match relation {
            Relation::Binary { left, right, typ } => {
                let (position, binop) = match (outer_var == left, outer_var == right) {
                    (true, false) => match typ {
                        Binop::AssociatedCallSite => return None,
                        Binop::Both | Binop::Control | Binop::Data => (Position::Source, typ),
                    },
                    (false, true) => match typ {
                        Binop::AssociatedCallSite => return None,
                        Binop::Both | Binop::Control | Binop::Data => (Position::Target, typ),
                    },
                    (true, true) | (false, false) => return None,
                };
                Some((position, binop.clone()))
            }
            Relation::IsMarked(..) => None,
            Relation::Negation(relation) => get_binop_and_position(relation, outer_var),
        }
    }
    /// Given a reference to a node in the policy, return its replacement fused node if possible;
    /// otherwise, return the original node
    fn process_node(node: &ASTNode, state: &mut FuseState) -> ASTNode {
        match node {
            ASTNode::Clause(clause) => {
                match &clause.intro {
                    ClauseIntro::ForEach(var_intro) | ClauseIntro::ThereIs(var_intro) => {
                        // Only support double loops of "variable marked" for now
                        match var_intro.intro {
                            VariableIntroType::AllNodes
                            | VariableIntroType::Roots
                            | VariableIntroType::VariableSourceOf(_)
                            | VariableIntroType::Variable => state.reset(),
                            VariableIntroType::VariableMarked { .. } => {
                                state.update_vars(var_intro.variable.clone());

                                if state.ready_to_fuse {
                                    // Look ahead to see if the body is a conditional or relation we can fuse
                                    match &clause.body {
                                        ASTNode::Clause(inner_clause) => {
                                            if let ClauseIntro::Conditional(relation) =
                                                &inner_clause.intro
                                            {
                                                let mut body_state = FuseState::default();
                                                let new_body = process_node(
                                                    &inner_clause.body,
                                                    &mut body_state,
                                                );
                                                if let Some(fused) = state.try_create_fused_clause(
                                                    relation,
                                                    var_intro,
                                                    Some(new_body),
                                                    true,
                                                ) {
                                                    return fused;
                                                }
                                            }
                                        }
                                        ASTNode::Relation(relation) => {
                                            if let Some(fused) = state.try_create_fused_clause(
                                                relation, var_intro, None, false,
                                            ) {
                                                return fused;
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                        }
                    }
                    ClauseIntro::Conditional(_) => {
                        state.reset();
                    }
                }

                let new_body = process_node(&clause.body, state);
                ASTNode::Clause(Box::new(Clause {
                    intro: clause.intro.clone(),
                    body: new_body,
                }))
            }
            ASTNode::Relation(_) => node.clone(),
            ASTNode::JoinedNodes(_) => {
                state.reset();
                node.clone()
            }
            ASTNode::OnlyVia(..) => {
                state.reset();
                node.clone()
            }
            ASTNode::FusedClause(_) => {
                unreachable!(
                    "Encountered a fused node before inserting any.
                    This indicates a compiler bug; fusing must come after lifting."
                )
            }
        }
    }

    let mut state = FuseState::default();
    let new_body = process_node(&original_policy.body, &mut state);

    Policy {
        body: new_body,
        ..original_policy.clone()
    }
}

pub fn optimize(policy: &mut Policy) -> Policy {
    lift_definitions(policy);
    fuse(policy.clone())
}
