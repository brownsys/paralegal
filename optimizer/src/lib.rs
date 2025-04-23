use std::collections::HashSet;

use common::{ast::*, Policy};

pub fn optimize(policy: &mut Policy) {
    // Steps:
    // - if the body doesn't contain any joins (just makes my life easier to start with)
    //   that implies that each variable can only be defined once, since we check scope
    // - so then go through each of the VariableIntros, get all the kinds VariableMarked
    // - replace all of those ^ with VariableIntroType::Variable
    // - move the original VariableIntro into a new definition

    // For simplicity, don't add new definitions if some already exist
    if !policy.definitions.is_empty() {
        return;
    }

    let og_policy = policy.clone();

    let mut intros: HashSet<VariableIntro> = HashSet::new();

    let mut queue: Vec<&mut ASTNode> = vec![];
    queue.push(&mut policy.body);

    while !queue.is_empty() {
        let node = queue.pop().unwrap();
        match node {
            ASTNode::Clause(clause) => {
                match &mut clause.intro {
                    ClauseIntro::ForEach(var_intro) | ClauseIntro::ThereIs(var_intro) => {
                        if !intros.contains(&var_intro) {
                            intros.insert(var_intro.clone());
                        }
                        var_intro.intro = VariableIntroType::Variable;
                    }
                    ClauseIntro::Conditional(_) => {}
                }
                queue.push(&mut clause.body);
            }
            // bail if we encounter any joins for now
            // bc joins allow defining the same variable twice with different markers
            // and this optimization assumes that everything is only defined once
            // so that it's ok to move everything to the top
            ASTNode::JoinedNodes(_) => {
                *policy = og_policy;
                return;
            }
            _ => {}
        }
    }

    policy.definitions = intros
        .into_iter()
        .map(|var_intro| {
            Definition {
                variable: var_intro.variable.clone(),
                scope: DefinitionScope::Ctrler,
                // this is what really matters, since the template ends up just rendering this intro since filter is None
                declaration: var_intro,
                filter: None,
            }
        })
        .collect::<Vec<_>>();

    // Easier for the user to have variable declarations in alphabetical order
    // Also easier for us when we're writing tests below
    policy
        .definitions
        .sort_by(|a, b| a.variable.cmp(&b.variable));

    dbg!(policy);
}

#[cfg(test)]
mod tests {
    use crate::*;
    use common::*;

    #[test]
    #[cfg(later)]
    fn freedit_store_date() {
        let mut policy = Policy {
            definitions: vec![Definition {
                variable: "pageview_store".into(),
                scope: DefinitionScope::Ctrler,
                declaration: VariableIntro {
                    variable: "store".into(),
                    intro: VariableIntroType::VariableMarked {
                        marker: "db_store".into(),
                        on_type: false,
                    },
                },
                filter: Some(ASTNode::Clause(Box::new(Clause {
                    intro: ClauseIntro::ThereIs(VariableIntro {
                        variable: "pageview".into(),
                        intro: VariableIntroType::VariableMarked {
                            marker: "pageviews".into(),
                            on_type: false,
                        },
                    }),
                    body: ASTNode::Relation(Relation::Binary {
                        left: "pageview".into(),
                        right: "store".into(),
                        typ: Binop::Data,
                    }),
                }))),
            }],
            scope: PolicyScope::Everywhere,
            body: ASTNode::Clause(Box::new(Clause {
                intro: ClauseIntro::ForEach(VariableIntro {
                    variable: "pageview_store".into(),
                    intro: VariableIntroType::Variable,
                }),
                body: ASTNode::Clause(Box::new(Clause {
                    intro: ClauseIntro::ThereIs(VariableIntro {
                        variable: "date".into(),
                        intro: VariableIntroType::VariableMarked {
                            marker: "time".into(),
                            on_type: false,
                        },
                    }),
                    body: ASTNode::Relation(Relation::Binary {
                        left: "date".into(),
                        right: "pageview_store".into(),
                        typ: Binop::Data,
                    }),
                })),
            })),
        };
        // no optimizations possible
        let optimized_policy = policy.clone();
        optimize(&mut policy);
        assert_eq!(policy, optimized_policy);
    }

    #[test]
    fn hyperswitch_card_storage() {
        let mut policy = Policy {
            definitions: vec![],
            scope: PolicyScope::Everywhere,
            body: ASTNode::Clause(Box::new(Clause {
                intro: ClauseIntro::ForEach(VariableIntro {
                    variable: "card".into(),
                    intro: VariableIntroType::VariableMarked {
                        marker: "credit_card".into(),
                        on_type: false,
                    },
                }),
                body: ASTNode::Clause(Box::new(Clause {
                    intro: ClauseIntro::ForEach(VariableIntro {
                        variable: "store".into(),
                        intro: VariableIntroType::VariableMarked {
                            marker: "store".into(),
                            on_type: false,
                        },
                    }),
                    body: ASTNode::Clause(Box::new(Clause {
                        intro: ClauseIntro::Conditional(Relation::Binary {
                            left: "card".into(),
                            right: "store".into(),
                            typ: Binop::Data,
                        }),
                        body: ASTNode::Clause(Box::new(Clause {
                            intro: ClauseIntro::ThereIs(VariableIntro {
                                variable: "consent".into(),
                                intro: VariableIntroType::VariableMarked {
                                    marker: "future_usage_decision".into(),
                                    on_type: false,
                                },
                            }),
                            body: ASTNode::Relation(Relation::Binary {
                                left: "consent".into(),
                                right: "store".into(),
                                typ: Binop::Control,
                            }),
                        })),
                    })),
                })),
            })),
        };
        let optimized_policy = Policy {
            definitions: vec![
                Definition {
                    variable: "card".into(),
                    scope: DefinitionScope::Ctrler,
                    declaration: VariableIntro {
                        variable: "card_inner".into(),
                        intro: VariableIntroType::VariableMarked {
                            marker: "credit_card".into(),
                            on_type: false,
                        },
                    },
                    filter: None,
                },
                Definition {
                    variable: "consent".into(),
                    scope: DefinitionScope::Ctrler,
                    declaration: VariableIntro {
                        variable: "consent_inner".into(),
                        intro: VariableIntroType::VariableMarked {
                            marker: "future_usage_decision".into(),
                            on_type: false,
                        },
                    },
                    filter: None,
                },
                Definition {
                    variable: "store".into(),
                    scope: DefinitionScope::Ctrler,
                    declaration: VariableIntro {
                        variable: "store_inner".into(),
                        intro: VariableIntroType::VariableMarked {
                            marker: "store".into(),
                            on_type: false,
                        },
                    },
                    filter: None,
                },
            ],
            scope: PolicyScope::Everywhere,
            body: ASTNode::Clause(Box::new(Clause {
                intro: ClauseIntro::ForEach(VariableIntro {
                    variable: "card".into(),
                    intro: VariableIntroType::Variable,
                }),
                body: ASTNode::Clause(Box::new(Clause {
                    intro: ClauseIntro::ForEach(VariableIntro {
                        variable: "store".into(),
                        intro: VariableIntroType::Variable,
                    }),
                    body: ASTNode::Clause(Box::new(Clause {
                        intro: ClauseIntro::Conditional(Relation::Binary {
                            left: "card".into(),
                            right: "store".into(),
                            typ: Binop::Data,
                        }),
                        body: ASTNode::Clause(Box::new(Clause {
                            intro: ClauseIntro::ThereIs(VariableIntro {
                                variable: "consent".into(),
                                intro: VariableIntroType::Variable,
                            }),
                            body: ASTNode::Relation(Relation::Binary {
                                left: "consent".into(),
                                right: "store".into(),
                                typ: Binop::Control,
                            }),
                        })),
                    })),
                })),
            })),
        };

        optimize(&mut policy);
        assert_eq!(policy, optimized_policy);
    }
}
