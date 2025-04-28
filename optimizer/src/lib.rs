use common::{ast::*, Policy};

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
        match node {
            ASTNode::Clause(clause) => {
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
            ASTNode::JoinedNodes(obligation) => {
                queue.push(&obligation.src);
                queue.push(&obligation.sink);
            }
            ASTNode::Relation(ref relation) => {
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
            ASTNode::OnlyVia(_, _, _) => {
                return;
            }
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
}

// Search for this pattern:
// 1. For A marked a:
//   A. For B marked b:
//     a. If BinaryRelation(A, B), then: ...
// and replace the inner clause with a FusedClause
// TODO: it would be nice if this could mutate the policy in-place, but I gave up after fighting with the borrow checker for awhile.
// I'm not sure it's trivial to do that.
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
                        Binop::AssociatedCallSite | Binop::Control => return None,
                        Binop::Both | Binop::Data => (Position::Source, typ),
                    },
                    (false, true) => match typ {
                        Binop::AssociatedCallSite | Binop::Control => return None,
                        Binop::Both | Binop::Data => (Position::Target, typ),
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
