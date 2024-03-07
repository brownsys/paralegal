use nom::{
    branch::alt,
    bytes::complete::tag,
    error::context,
    sequence::{separated_pair, terminated, tuple, delimited, preceded}, character::complete::{space0, space1}, combinator::opt,
};

use crate::{
    ASTNode, TwoVarRelation, Res, common::*, OnlyViaRelation, variable_intro::{variable_intro, variable_marked, variable_def},
};

// this is flows_to(EdgeSelection::DataAndControl)
fn influences_relation<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "influences relation",
        separated_pair(
            variable, 
            tuple((tag("influences"), space1)),
            variable
        )
    );
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        ASTNode::Influences(TwoVarRelation {
            src: var1,
            dest: var2,
        }),
    ))
}

// this is flows_to(EdgeSelection::Data)
fn goes_to_relation<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "goes to relation", 
        separated_pair(
            variable, 
            tuple((tag("goes to"), space1)),
            variable
        )
    );
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        ASTNode::FlowsTo(TwoVarRelation {
            src: var1,
            dest: var2,
        }),
    ))
}

fn does_not_go_to_relation<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "does not go to relation", 
        separated_pair(
            variable, 
            tag("does not go to"), 
            variable
        )
    );
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        ASTNode::NoFlowsTo(TwoVarRelation {
            src: var1,
            dest: var2,
        }),
    ))
}

fn operation_associated_with_relation<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "operation associated with relation",
        separated_pair(
            variable, 
            tag("goes to the operation associated with"), 
            variable
        )
    );
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        ASTNode::AssociatedCallSite(TwoVarRelation {
            src: var1,
            dest: var2,
        }),
    ))
}

fn affects_whether_relation<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "affects whether relation",
        tuple((
            terminated(variable, tag("affects whether")),
            terminated(variable, tag("happens"))
        )),
    );
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        ASTNode::ControlFlow(TwoVarRelation {
            src: var1,
            dest: var2,
        }),
    ))
}

fn does_not_affects_whether_relation<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "does not affects whether relation",
        tuple((
            terminated(variable, tag("does not affect whether")),
            terminated(variable, tag("happens"))
        )),
    );
    let (remainder, (var1, var2)) = combinator(s)?;

    Ok((
        remainder,
        ASTNode::NoControlFlow(TwoVarRelation {
            src: var1,
            dest: var2,
        }),
    ))
}

fn is_marked_relation<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "is marked relation",
        separated_pair(
            variable,
            tag("is marked"),
            marker,
        )
    );
    let (remainder, (var, marker)) = combinator(s)?;

    Ok((
        remainder,
        ASTNode::IsMarked((var, marker))
    ))
}

fn is_not_marked_relation<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "is marked relation",
        separated_pair(
            variable,
            tag("is not marked"),
            marker,
        )
    );
    let (remainder, (var, marker)) = combinator(s)?;

    Ok((
        remainder,
        ASTNode::IsNotMarked((var, marker)),
    ))
}

pub fn only_via_relation<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    let mut combinator = context(
        "only via relation",
        tuple((
            delimited(tuple((space0, tag("each"), space1)), variable_intro, tag("goes to a")),
            alt((variable_marked, variable_def)),
            preceded(
                tag("only via a"),
                alt((variable_marked, variable_def)),
            ) 
        ))
    );
    let (remainder, (src, dest, checkpoint)) = combinator(s)?;

    Ok((
        remainder,
        ASTNode::OnlyVia(OnlyViaRelation{src, dest, checkpoint})
    ))
}

pub fn relation<'a>(s: &'a str) -> Res<&str, ASTNode<'a>> {
    context(
        "relation",
        alt((
            // must try only via before goes to since goes to will partially consume an only via
            only_via_relation,
            goes_to_relation,
            does_not_go_to_relation,
            affects_whether_relation,
            does_not_affects_whether_relation,
            is_marked_relation,
            is_not_marked_relation,
            influences_relation,
            operation_associated_with_relation,
        ))
    )(s)
}




/*
#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    pub fn test_scope() {
        let always = "always:";
        let sometimes = "sometimes:";
        let always_w_punc = "\nalways: \n";
        let sometimes_w_punc = "\nsometimes: \n";

        assert_eq!(scope(always), Ok(("", PolicyScope::Always)));
        assert_eq!(scope(always_w_punc), Ok(("", PolicyScope::Always)));
        assert_eq!(scope(sometimes), Ok(("", PolicyScope::Sometimes)));
        assert_eq!(scope(sometimes_w_punc), Ok(("", PolicyScope::Sometimes)));
    }

    #[test]
    pub fn test_alphabetic_w_underscores() {
        let no_underscores = "var";
        let one_underscore = "hello_world";
        let two_underscores = "community_delete_check";
        let trailing_underscore = "hello_world_";
        let five_underscores = "this_is_a_long_variable";

        assert_eq!(
            alphabetic_w_underscores(no_underscores),
            Ok(("", no_underscores))
        );
        assert_eq!(
            alphabetic_w_underscores(one_underscore),
            Ok(("", one_underscore))
        );
        assert_eq!(
            alphabetic_w_underscores(two_underscores),
            Ok(("", two_underscores))
        );
        assert_eq!(
            alphabetic_w_underscores(trailing_underscore),
            Ok(("", trailing_underscore))
        );
        assert_eq!(
            alphabetic_w_underscores(five_underscores),
            Ok(("", five_underscores))
        );

        // these are errors for now, but don't need to be
        let leading_underscore = "_hello_world";
        let two_consec_underscores = "multiple__underscores";
        assert!(alphabetic_w_underscores(leading_underscore).is_err());
        assert!(all_consuming(alphabetic_w_underscores)(two_consec_underscores).is_err());
    }

    #[test]
    pub fn test_marker() {
        let a = "\"a\"";
        let b = "\"sensitive\"";
        let err1 = "sensitive";
        let err2 = "\"sensitive";

        assert_eq!(marker(a), Ok(("", "a")));
        assert_eq!(marker(b), Ok(("", "sensitive")));
        assert!(marker(err1).is_err());
        assert!(marker(err2).is_err());
    }

    #[test]
    pub fn test_variable() {
        let var1 = "a";
        let var2 = "sensitive";
        let wrong = "123hello";
        let partially_keyword = "a flows to b";

        assert_eq!(variable(var1), Ok(("", "a")));
        assert_eq!(variable(var2), Ok(("", "sensitive")));
        assert_eq!(
            variable(partially_keyword),
            Ok((" flows to b", "a"))
        );
        assert!(variable(wrong).is_err());
    }

    #[test]
    pub fn test_goes_to_or_only_via_relation() {
        let policy1 = "a flows to b";
        let policy1_ans = ASTNode::FlowsTo(TwoVarRelation {src: "a", dest: "b"});
        let policy2 = "a flows to b only via c";
        let policy2_ans = ASTNode::OnlyVia(ThreeVarObligation {src: "a", dest: "b", checkpoint: "c"});
        
        let err1 = "a has control flow influence on b";
        let err2 = "a flows to b only via c only via d";

        assert_eq!(goes_to_or_only_via_relation(policy1), Ok(("", policy1_ans)));
        assert_eq!(goes_to_or_only_via_relation(policy2), Ok(("", policy2_ans)));
        assert!(goes_to_or_only_via_relation(err1).is_err());
        assert_eq!(goes_to_or_only_via_relation(err2), Ok((" only via d", ASTNode::OnlyVia(ThreeVarObligation { src: "a", dest: "b", checkpoint: "c" }))));
    }

    #[test]
    pub fn test_body() {
        let only via = "a flows to b only via c";
        let only via_ans = ASTNode::OnlyVia(ThreeVarObligation {
            src: "a",
            dest: "b" ,
            checkpoint: "c" 
        });

        let goes_to = "a flows to b";
        let goes_to_ans = ASTNode::FlowsTo(TwoVarRelation {
            src: "a" ,
            dest: "b" 
        });
        let affects_whether = "a has control flow influence on b";
        let affects_whether_ans = ASTNode::ControlFlow(TwoVarRelation {
            src: "a",
            dest: "b" 
        });

        let joined1 = "a flows to b and a flows to b only via c";
        let joined1_ans = ASTNode::And(
            Box::new(
                TwoNodeObligation {
                    src: ASTNode::FlowsTo(TwoVarRelation {
                        src: "a", 
                        dest: "b" 
                    }),
                    dest: ASTNode::OnlyVia(ThreeVarObligation {
                        src: "a", 
                        dest: "b",
                        checkpoint: "c" 
                    }),
                }
            )
        );

        let joined2 = "a flows to b and a flows to b only via c or a has control flow influence on b";
        let joined2_ans = ASTNode::And(
            Box::new(
                TwoNodeObligation {
                    src: ASTNode::FlowsTo(TwoVarRelation {
                        src: "a", 
                        dest: "b" 
                    }),
                    dest: ASTNode::Or(
                        Box::new(
                            TwoNodeObligation {
                                src: ASTNode::OnlyVia(
                                    ThreeVarObligation {
                                        src: "a", 
                                        dest: "b",
                                        checkpoint: "c"
                                    }),
                                dest: ASTNode::ControlFlow(
                                    TwoVarRelation {
                                        src: "a", 
                                        dest: "b" 
                                    }),
                            }
                        )),
                }
            )
        );

        let joined3 = "a has control flow influence on b implies a flows to c and b flows to c";
        let joined3_ans = ASTNode::Implies(Box::new(TwoNodeObligation {
            src: ASTNode::ControlFlow(TwoVarRelation{
                src: "a",
                dest: "b",
            }),
            dest: ASTNode::And(
                Box::new(
                    TwoNodeObligation {
                        src: ASTNode::FlowsTo(TwoVarRelation {
                            src: "a", 
                            dest: "c" 
                        }),
                        dest: ASTNode::FlowsTo(TwoVarRelation {
                            src: "b", 
                            dest: "c" 
                        }),
                    }
                ))
        }));

        let err1 = "a flows to";
        let err2 = "a flows to b only via";
        let err3 = "a has control flow influence on";

        assert_eq!(body(only via), Ok(("", only via_ans)));
        assert_eq!(body(goes_to), Ok(("", goes_to_ans)));
        assert_eq!(body(affects_whether), Ok(("", affects_whether_ans)));
        assert_eq!(body(joined1), Ok(("", joined1_ans)));
        assert_eq!(body(joined2), Ok(("", joined2_ans)));
        assert_eq!(body(joined3), Ok(("", joined3_ans)));
        assert!(body(err1).is_err());
        assert_eq!(body(err2), Ok((" only via", ASTNode::FlowsTo(TwoVarRelation {src: "a", dest: "b"}))));
        assert!(body(err3).is_err());
    }


    #[test]
    pub fn test_variable_clause() {
        let simple_body = 
            "all dc : \"delete_check\" ( 
                dc flows to sink
            )";
        
        let simple_body_ans =
            ASTNode::VarIntroduction(Box::new(VariableClause {
                binding: VariableBinding {quantifier: Quantifier::All, variable: "dc", marker: "delete_check"},
                body: ASTNode::FlowsTo(TwoVarRelation{src: "dc", dest: "sink"})
            }));
        
        let joined_body =
            "all dc : \"delete_check\" ( 
                dc flows to sink or dc flows to encrypts and dc flows to source
            )";
        let joined_body_ans =
            ASTNode::VarIntroduction(Box::new (VariableClause {
                binding: VariableBinding {quantifier: Quantifier::All, variable: "dc", marker: "delete_check"},
                body: ASTNode::Or(
                    Box::new(TwoNodeObligation {
                        src: ASTNode::FlowsTo(TwoVarRelation{src: "dc", dest: "sink"}),
                        dest: ASTNode::And(Box::new(TwoNodeObligation {
                            src: ASTNode::FlowsTo(TwoVarRelation{src: "dc", dest: "encrypts"}),
                            dest: ASTNode::FlowsTo(TwoVarRelation{src: "dc", dest: "source"}),
                        }))
                    })
                ) 
            }));

        let triple_nested = 
            "some a : \"a\" (
                some b : \"b\" (
                    some c : \"c\" (
                        a flows to c
                    )
                )
            )";
        let triple_nested_ans =
        ASTNode::VarIntroduction(Box::new(VariableClause {
            binding: VariableBinding {quantifier: Quantifier::Some, variable: "a", marker: "a"},
            body: ASTNode::VarIntroduction(Box::new(VariableClause {
                binding: VariableBinding {quantifier: Quantifier::Some, variable: "b", marker: "b"},
                body: ASTNode::VarIntroduction(Box::new(VariableClause {
                    binding: VariableBinding {quantifier: Quantifier::Some, variable: "c", marker: "c"},
                    body: ASTNode::FlowsTo(TwoVarRelation{src: "a", dest: "c"})
                }))
            }))
        }));

        let lemmy_comm = "
        some comm_data : \"community_data\" (
            all write : \"db_write\" (
                comm_data flows to write
                implies
                some comm_dc : \"community_delete_check\" (
                    comm_data flows to comm_dc
                    and
                    comm_dc has control flow influence on write
                ) and
                some comm_bc : \"community_ban_check\" (
                    comm_data flows to comm_bc
                    and
                    comm_bc has control flow influence on write
                )
            )
        )";
        let lemmy_comm_ans = ASTNode::VarIntroduction(Box::new(VariableClause {
            binding: VariableBinding { quantifier: Quantifier::Some, variable: "comm_data", marker: "community_data" },
            body: ASTNode::VarIntroduction(Box::new(VariableClause { 
                binding: VariableBinding { quantifier: Quantifier::All, variable: "write", marker: "db_write" }, 
                body: ASTNode::Implies(Box::new(TwoNodeObligation { 
                    src: ASTNode::FlowsTo(TwoVarRelation { src: "comm_data", dest: "write" }), 
                    dest: ASTNode::And(Box::new(TwoNodeObligation{
                        src: ASTNode::VarIntroduction(Box::new(VariableClause { 
                            binding: VariableBinding { quantifier: Quantifier::Some, variable: "comm_dc", marker: "community_delete_check" }, 
                            body: ASTNode::And(Box::new(TwoNodeObligation { 
                                src: ASTNode::FlowsTo(TwoVarRelation { src: "comm_data", dest: "comm_dc" }), 
                                dest: ASTNode::ControlFlow(TwoVarRelation { src: "comm_dc", dest: "write" })
                            })) 
                        })),
                        dest: ASTNode::VarIntroduction(Box::new(VariableClause { 
                            binding: VariableBinding { quantifier: Quantifier::Some, variable: "comm_bc", marker: "community_ban_check" }, 
                            body: ASTNode::And(Box::new(TwoNodeObligation { 
                                src: ASTNode::FlowsTo(TwoVarRelation { src: "comm_data", dest: "comm_bc" }), 
                                dest: ASTNode::ControlFlow(TwoVarRelation { src: "comm_bc", dest: "write" })
                            })) 
                        })),
                    }))
                }))
            }))
        }));

        // should only parse the first *top level* variable clause
        let lemmy_inst = 
        "some dc: \"instance_delete_check\" (
            all write : \"db_write\" (
                dc has control flow influence on write
            )
            and
            all read: \"db_read\" (
                dc has control flow influence on read
            )
        ) and 
        some bc : \"instance_ban_check\" (
            all write : \"db_write\" (
                bc has control flow influence on write
            )
            and
            all read: \"db_read\" (
                bc has control flow influence on read
            )
        )";
        let lemmy_inst_partial = ASTNode::VarIntroduction(Box::new(VariableClause {
                binding: VariableBinding { quantifier: Quantifier::Some, variable: "dc", marker: "instance_delete_check" },
                body: ASTNode::And(Box::new(TwoNodeObligation {
                    src: ASTNode::VarIntroduction(Box::new(VariableClause {
                        binding: VariableBinding {quantifier: Quantifier::All, variable: "write", marker: "db_write"},
                        body: ASTNode::ControlFlow(TwoVarRelation { src: "dc", dest: "write"})
                        })),
                    dest: ASTNode::VarIntroduction(Box::new(VariableClause {
                        binding: VariableBinding {quantifier: Quantifier::All, variable: "read", marker: "db_read"},
                        body: ASTNode::ControlFlow(TwoVarRelation { src: "dc", dest: "read"})
                        })),
                    }))
            }));
        let lemmy_inst_leftover = "and 
        some bc : \"instance_ban_check\" (
            all write : \"db_write\" (
                bc has control flow influence on write
            )
            and
            all read: \"db_read\" (
                bc has control flow influence on read
            )
        )";

        // should be able to parse anything that joined_clauses can
        // as long as it's wrapped in a variable binding
        let wrapped =
            "some dc : \"delete_check\" (
                dc flows to sink or dc flows to encrypts only via bc and dc has control flow influence on source
                implies
                all dc : \"delete_check\" ( 
                    dc flows to sink or dc flows to encrypts only via bc and dc has control flow influence on source
                )
            )";
        
        let clause_with_joined_body_ans = 
            ASTNode::Implies(
                Box::new(TwoNodeObligation {
                    src: ASTNode::Or(Box::new(TwoNodeObligation {
                        src: ASTNode::FlowsTo(TwoVarRelation {src: "dc", dest: "sink"}),
                        dest: ASTNode::And(
                            Box::new(TwoNodeObligation {
                                src: ASTNode::OnlyVia(ThreeVarObligation {src: "dc", dest: "encrypts", checkpoint: "bc"}),
                                dest: ASTNode::ControlFlow(TwoVarRelation {src: "dc", dest: "source"})
                            }))
                        })),
                    dest: ASTNode::VarIntroduction(
                        Box::new(VariableClause {
                            binding : VariableBinding {quantifier: Quantifier::All, variable: "dc", marker: "delete_check"},
                            body: ASTNode::Or(Box::new(TwoNodeObligation {
                                src: ASTNode::FlowsTo(TwoVarRelation {src: "dc", dest: "sink"}),
                                dest: ASTNode::And(
                                    Box::new(TwoNodeObligation {
                                        src: ASTNode::OnlyVia(ThreeVarObligation {src: "dc", dest: "encrypts", checkpoint: "bc"}),
                                        dest: ASTNode::ControlFlow(TwoVarRelation {src: "dc", dest: "source"})
                                    }))
                            }))
                        }))
             }));

             let wrapped_ans = ASTNode::VarIntroduction(Box::new(VariableClause {
                binding: VariableBinding {quantifier: Quantifier::Some, variable: "dc", marker: "delete_check"},
                body: clause_with_joined_body_ans,
             }));

        assert_eq!(variable_clause(simple_body), Ok(("", simple_body_ans)));
        assert_eq!(variable_clause(joined_body), Ok(("", joined_body_ans)));
        assert_eq!(variable_clause(triple_nested), Ok(("", triple_nested_ans)));
        assert_eq!(variable_clause(lemmy_comm), Ok(("", lemmy_comm_ans)));
        assert_eq!(variable_clause(lemmy_inst), Ok((lemmy_inst_leftover, lemmy_inst_partial)));
        assert_eq!(variable_clause(wrapped), Ok(("", wrapped_ans)));
    }

    #[test]
    pub fn test_joined_clauses() {
        let two_bodies = "a flows to b and b flows to c";
        let three_bodies = "a flows to b and b flows to c and a flows to c";

        let clause_with_simple_body_w_joined_variable_clauses = 
            "all dc : \"delete_check\" ( 
                dc flows to sink or dc flows to encrypts only via bc and dc has control flow influence on source
            ) or
            all dc : \"delete_check\" ( 
                dc flows to sink
            ) and
            all dc : \"delete_check\" ( 
                all dc : \"delete_check\" ( 
                    dc flows to sink
                )
            )";
        let clause_with_simple_body_w_joined_variable_clauses_ans = 
            ASTNode::Or(
                Box::new(TwoNodeObligation {
                    src: ASTNode::VarIntroduction(
                        Box::new(VariableClause {
                            binding : VariableBinding {quantifier: Quantifier::All, variable: "dc", marker: "delete_check"},
                            body: ASTNode::Or(Box::new(TwoNodeObligation {
                                src: ASTNode::FlowsTo(TwoVarRelation {src: "dc", dest: "sink"}),
                                dest: ASTNode::And(
                                    Box::new(TwoNodeObligation {
                                        src: ASTNode::OnlyVia(ThreeVarObligation {src: "dc", dest: "encrypts", checkpoint: "bc"}),
                                        dest: ASTNode::ControlFlow(TwoVarRelation {src: "dc", dest: "source"})
                                    }))
                            }))
                    })),
                    dest: ASTNode::And(Box::new(TwoNodeObligation {
                        src: ASTNode::VarIntroduction(
                            Box::new(VariableClause {
                                binding : VariableBinding {quantifier: Quantifier::All, variable: "dc", marker: "delete_check"},
                                body: ASTNode::FlowsTo(TwoVarRelation {src: "dc", dest: "sink"}),
                            })),
                        dest: ASTNode::VarIntroduction(
                            Box::new(VariableClause {
                                binding : VariableBinding {quantifier: Quantifier::All, variable: "dc", marker: "delete_check"},
                                body: ASTNode::VarIntroduction(
                                    Box::new(VariableClause {
                                        binding : VariableBinding {quantifier: Quantifier::All, variable: "dc", marker: "delete_check"},
                                        body: ASTNode::FlowsTo(TwoVarRelation {src: "dc", dest: "sink"}),
                                    }))
                            }))
                    })) 
            }));
        
        let clause_with_simple_body_w_variable_clause = 
            "all dc : \"delete_check\" ( 
                dc flows to sink
            ) or
            all bc : \"ban_check\" ( 
                bc flows to sink
            )";
        
        let clause_with_simple_body_w_variable_clause_ans = 
            ASTNode::Or(
                Box::new(TwoNodeObligation {
                    src: ASTNode::VarIntroduction(
                        Box::new(VariableClause {
                            binding : VariableBinding {quantifier: Quantifier::All, variable: "dc", marker: "delete_check"},
                            body: ASTNode::FlowsTo(TwoVarRelation {src: "dc", dest: "sink"}),
                        })),
                    dest: ASTNode::VarIntroduction(
                        Box::new(VariableClause {
                            binding : VariableBinding {quantifier: Quantifier::All, variable: "bc", marker: "ban_check"},
                            body: ASTNode::FlowsTo(TwoVarRelation {src: "bc", dest: "sink"}),
                        })),
             }));
        
        let clause_with_joined_body =
            "dc flows to sink or dc flows to encrypts only via bc and dc has control flow influence on source
            implies
            all dc : \"delete_check\" ( 
                dc flows to sink or dc flows to encrypts only via bc and dc has control flow influence on source
            )";
        
        let clause_with_joined_body_ans = 
            ASTNode::Implies(
                Box::new(TwoNodeObligation {
                    src: ASTNode::Or(Box::new(TwoNodeObligation {
                        src: ASTNode::FlowsTo(TwoVarRelation {src: "dc", dest: "sink"}),
                        dest: ASTNode::And(
                            Box::new(TwoNodeObligation {
                                src: ASTNode::OnlyVia(ThreeVarObligation {src: "dc", dest: "encrypts", checkpoint: "bc"}),
                                dest: ASTNode::ControlFlow(TwoVarRelation {src: "dc", dest: "source"})
                            }))
                        })),
                    dest: ASTNode::VarIntroduction(
                        Box::new(VariableClause {
                            binding : VariableBinding {quantifier: Quantifier::All, variable: "dc", marker: "delete_check"},
                            body: ASTNode::Or(Box::new(TwoNodeObligation {
                                src: ASTNode::FlowsTo(TwoVarRelation {src: "dc", dest: "sink"}),
                                dest: ASTNode::And(
                                    Box::new(TwoNodeObligation {
                                        src: ASTNode::OnlyVia(ThreeVarObligation {src: "dc", dest: "encrypts", checkpoint: "bc"}),
                                        dest: ASTNode::ControlFlow(TwoVarRelation {src: "dc", dest: "source"})
                                    }))
                            }))
                        }))
             }));
        
        let multiple_bodies = 
            "dc flows to sink or dc flows to encrypts only via bc and dc has control flow influence on source
            and
            bc flows to encrypts
            implies
            all dc : \"delete_check\" ( 
                dc flows to sink or dc flows to encrypts only via bc and dc has control flow influence on source
            ) or
            dc flows to encrypts";

        let multiple_bodies_ans = ASTNode::Implies(
            Box::new(TwoNodeObligation { 
            // the four statements in the body
            src: ASTNode::Or(Box::new(TwoNodeObligation { 
                src: ASTNode::FlowsTo(TwoVarRelation { src: "dc", dest: "sink" }), 
                dest: ASTNode::And(Box::new(TwoNodeObligation { 
                    src: ASTNode::OnlyVia(ThreeVarObligation { src: "dc", dest: "encrypts", checkpoint: "bc" }), 
                    dest: ASTNode::And(Box::new(TwoNodeObligation { 
                        src: ASTNode::ControlFlow(TwoVarRelation { src: "dc", dest: "source" }), 
                        dest: ASTNode::FlowsTo(TwoVarRelation { src: "bc", dest: "encrypts" })}))}))})), 
            // "implies" the rest
            dest: ASTNode::Or(Box::new(TwoNodeObligation { 
                src: ASTNode::VarIntroduction(Box::new(VariableClause { 
                    binding: VariableBinding { quantifier: Quantifier::All, variable: "dc", marker: "delete_check" }, 
                    body: ASTNode::Or(Box::new(TwoNodeObligation { 
                        src: ASTNode::FlowsTo(TwoVarRelation { src: "dc", dest: "sink" }), 
                        dest: ASTNode::And(Box::new(TwoNodeObligation { 
                            src: ASTNode::OnlyVia(ThreeVarObligation { src: "dc", dest: "encrypts", checkpoint: "bc" }), 
                            dest: ASTNode::ControlFlow(TwoVarRelation { src: "dc", dest: "source" }) }))}))})), 
                dest: ASTNode::FlowsTo(TwoVarRelation { src: "dc", dest: "encrypts" }) })) }));
        
        
        assert_eq!(joined_clauses(clause_with_simple_body_w_joined_variable_clauses), Ok(("", clause_with_simple_body_w_joined_variable_clauses_ans)));
        assert_eq!(joined_clauses(clause_with_simple_body_w_variable_clause), Ok(("", clause_with_simple_body_w_variable_clause_ans)));
        assert_eq!(joined_clauses(clause_with_joined_body), Ok(("", clause_with_joined_body_ans)));
        assert_eq!(joined_clauses(multiple_bodies), Ok(("", multiple_bodies_ans)));
        // errors b/c body already covers multiple conjoined bodies
        // this parser gets >1 body joined *with* variable clauses
        assert!(joined_clauses(two_bodies).is_err());
        assert!(joined_clauses(three_bodies).is_err());
    }

    #[test]
    pub fn test_joined_variable_clauses() {
        let lemmy_inst = 
        "some dc: \"instance_delete_check\" (
            all write : \"db_write\" (
                dc has control flow influence on write
            )
            and
            all read: \"db_read\" (
                dc has control flow influence on read
            )
        ) and 
        some bc : \"instance_ban_check\" (
            all write : \"db_write\" (
                bc has control flow influence on write
            )
            and
            all read: \"db_read\" (
                bc has control flow influence on read
            )
        )";
        let lemmy_inst_ans = ASTNode::And(Box::new(TwoNodeObligation {
            src: ASTNode::VarIntroduction(Box::new(VariableClause {
                binding: VariableBinding { quantifier: Quantifier::Some, variable: "dc", marker: "instance_delete_check" },
                body: ASTNode::And(Box::new(TwoNodeObligation {
                    src: ASTNode::VarIntroduction(Box::new(VariableClause {
                        binding: VariableBinding {quantifier: Quantifier::All, variable: "write", marker: "db_write"},
                        body: ASTNode::ControlFlow(TwoVarRelation { src: "dc", dest: "write"})
                        })),
                    dest: ASTNode::VarIntroduction(Box::new(VariableClause {
                        binding: VariableBinding {quantifier: Quantifier::All, variable: "read", marker: "db_read"},
                        body: ASTNode::ControlFlow(TwoVarRelation { src: "dc", dest: "read"})
                        })),
                    }))
                })),
            dest: ASTNode::VarIntroduction(Box::new(VariableClause {
                binding: VariableBinding { quantifier: Quantifier::Some, variable: "bc", marker: "instance_ban_check" },
                body: ASTNode::And(Box::new(TwoNodeObligation {
                    src: ASTNode::VarIntroduction(Box::new(VariableClause {
                        binding: VariableBinding {quantifier: Quantifier::All, variable: "write", marker: "db_write"},
                        body: ASTNode::ControlFlow(TwoVarRelation { src: "bc", dest: "write"})
                        })),
                    dest: ASTNode::VarIntroduction(Box::new(VariableClause {
                        binding: VariableBinding {quantifier: Quantifier::All, variable: "read", marker: "db_read"},
                        body: ASTNode::ControlFlow(TwoVarRelation { src: "bc", dest: "read"})
                        })),
                    }))
                })),
        }));

        let triple_clauses = 
        "all dc : \"delete_check\" ( 
            dc flows to sink
        ) or
        all bc : \"ban_check\" ( 
            bc flows to sink
        ) and 
        all ec : \"encrypts_check\" ( 
            ec flows to sink
        )";
        
        let triple_clauses_ans =
            ASTNode::Or(
                Box::new(TwoNodeObligation {
                    src: ASTNode::VarIntroduction(
                        Box::new(VariableClause {
                            binding : VariableBinding {quantifier: Quantifier::All, variable: "dc", marker: "delete_check"},
                            body: ASTNode::FlowsTo(TwoVarRelation {src: "dc", dest: "sink"}),
                        })),
                    dest: ASTNode::And(Box::new(TwoNodeObligation { 
                        src: ASTNode::VarIntroduction(
                            Box::new(VariableClause {
                                binding : VariableBinding {quantifier: Quantifier::All, variable: "bc", marker: "ban_check"},
                                body: ASTNode::FlowsTo(TwoVarRelation {src: "bc", dest: "sink"}),
                            })),
                        dest: ASTNode::VarIntroduction(
                            Box::new(VariableClause {
                                binding : VariableBinding {quantifier: Quantifier::All, variable: "ec", marker: "encrypts_check"},
                                body: ASTNode::FlowsTo(TwoVarRelation {src: "ec", dest: "sink"}),
                            })),
                    }))
             }));
        
        // can't have bodies w/o bindings
        let multiple_bodies = 
            "dc flows to sink or dc flows to encrypts only via bc and dc has control flow influence on source
            and
            bc flows to encrypts
            implies
            all dc : \"delete_check\" ( 
                dc flows to sink or dc flows to encrypts only via bc and dc has control flow influence on source
            ) or
            dc flows to encrypts";
        
        let clause_with_joined_body =
            "dc flows to sink or dc flows to encrypts only via bc and dc has control flow influence on source
            implies
            all dc : \"delete_check\" ( 
                dc flows to sink or dc flows to encrypts only via bc and dc has control flow influence on source
            )";

        assert_eq!(joined_variable_clauses(lemmy_inst), Ok(("", lemmy_inst_ans)));
        assert_eq!(joined_variable_clauses(triple_clauses), Ok(("", triple_clauses_ans)));
        assert!(joined_variable_clauses(multiple_bodies).is_err());
        assert!(joined_variable_clauses(clause_with_joined_body).is_err());

    }

    #[test]
    pub fn test_parse() {
        let lemmy_inst = 
        "always:
        some dc: \"instance_delete_check\" (
            all write : \"db_write\" (
                dc has control flow influence on write
            )
            and
            all read: \"db_read\" (
                dc has control flow influence on read
            )
        ) and 
        some bc : \"instance_ban_check\" (
            all write : \"db_write\" (
                bc has control flow influence on write
            )
            and
            all read: \"db_read\" (
                bc has control flow influence on read
            )
        )";
        let lemmy_inst_ans = Policy {
            scope : PolicyScope::Always, 
            body: ASTNode::And(Box::new(TwoNodeObligation {
                src: ASTNode::VarIntroduction(Box::new(VariableClause {
                    binding: VariableBinding { quantifier: Quantifier::Some, variable: "dc", marker: "instance_delete_check" },
                    body: ASTNode::And(Box::new(TwoNodeObligation {
                        src: ASTNode::VarIntroduction(Box::new(VariableClause {
                            binding: VariableBinding {quantifier: Quantifier::All, variable: "write", marker: "db_write"},
                            body: ASTNode::ControlFlow(TwoVarRelation { src: "dc", dest: "write"})
                            })),
                        dest: ASTNode::VarIntroduction(Box::new(VariableClause {
                            binding: VariableBinding {quantifier: Quantifier::All, variable: "read", marker: "db_read"},
                            body: ASTNode::ControlFlow(TwoVarRelation { src: "dc", dest: "read"})
                            })),
                        }))
                    })),
                dest: ASTNode::VarIntroduction(Box::new(VariableClause {
                    binding: VariableBinding { quantifier: Quantifier::Some, variable: "bc", marker: "instance_ban_check" },
                    body: ASTNode::And(Box::new(TwoNodeObligation {
                        src: ASTNode::VarIntroduction(Box::new(VariableClause {
                            binding: VariableBinding {quantifier: Quantifier::All, variable: "write", marker: "db_write"},
                            body: ASTNode::ControlFlow(TwoVarRelation { src: "bc", dest: "write"})
                            })),
                        dest: ASTNode::VarIntroduction(Box::new(VariableClause {
                            binding: VariableBinding {quantifier: Quantifier::All, variable: "read", marker: "db_read"},
                            body: ASTNode::ControlFlow(TwoVarRelation { src: "bc", dest: "read"})
                            })),
                        }))
                    })),
                }))
            };

        let lemmy_comm = "
            always:
            some comm_data : \"community_data\" (
            all write : \"db_write\" (
                comm_data flows to write
                implies
                some comm_dc : \"community_delete_check\" (
                    comm_data flows to comm_dc
                    and
                    comm_dc has control flow influence on write
                ) and
                some comm_bc : \"community_ban_check\" (
                    comm_data flows to comm_bc
                    and
                    comm_bc has control flow influence on write
                )
            )
        )";
        let lemmy_comm_ans = Policy {
            scope: PolicyScope::Always,
            body: ASTNode::VarIntroduction(Box::new(VariableClause {
                binding: VariableBinding { quantifier: Quantifier::Some, variable: "comm_data", marker: "community_data" },
                body: ASTNode::VarIntroduction(Box::new(VariableClause { 
                    binding: VariableBinding { quantifier: Quantifier::All, variable: "write", marker: "db_write" }, 
                    body: ASTNode::Implies(Box::new(TwoNodeObligation { 
                        src: ASTNode::FlowsTo(TwoVarRelation { src: "comm_data", dest: "write" }), 
                        dest: ASTNode::And(Box::new(TwoNodeObligation{
                            src: ASTNode::VarIntroduction(Box::new(VariableClause { 
                                binding: VariableBinding { quantifier: Quantifier::Some, variable: "comm_dc", marker: "community_delete_check" }, 
                                body: ASTNode::And(Box::new(TwoNodeObligation { 
                                    src: ASTNode::FlowsTo(TwoVarRelation { src: "comm_data", dest: "comm_dc" }), 
                                    dest: ASTNode::ControlFlow(TwoVarRelation { src: "comm_dc", dest: "write" })
                                })) 
                            })),
                            dest: ASTNode::VarIntroduction(Box::new(VariableClause { 
                                binding: VariableBinding { quantifier: Quantifier::Some, variable: "comm_bc", marker: "community_ban_check" }, 
                                body: ASTNode::And(Box::new(TwoNodeObligation { 
                                    src: ASTNode::FlowsTo(TwoVarRelation { src: "comm_data", dest: "comm_bc" }), 
                                    dest: ASTNode::ControlFlow(TwoVarRelation { src: "comm_bc", dest: "write" })
                                })) 
                            })),
                        }))
                    }))
                }))
            }))
        };
        assert_eq!(parse(lemmy_comm), Ok(("", lemmy_comm_ans)));
        assert_eq!(parse(lemmy_inst), Ok(("", lemmy_inst_ans)));
    }
}
*/