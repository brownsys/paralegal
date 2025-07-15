//! This visitor is incomplete. For now we only use it to edit AST nodes and the
//! rule numbers and to count variables, so that's what the traversals reach. If
//! you need more functionality you have to add it.
use super::ast::*;
use crate::Policy;

pub trait VisitMut<'p> {
    #[allow(dead_code)]
    fn visit_policy_mut(&mut self, policy: &'p mut Policy) {
        super_visit_policy_mut(self, policy);
    }
    fn visit_definition_mut(&mut self, definition: &'p mut Definition) {
        super_visit_definition_mut(self, definition);
    }
    fn visit_ast_node_mut(&mut self, node: &'p mut ASTNode) {
        super_visit_ast_node_mut(self, node);
    }
    fn visit_variable_mut(&mut self, _variable: &'p mut Variable) {}
    fn visit_variable_intro_mut(&mut self, variable: &'p mut VariableIntro) {
        super_visit_variable_intro_mut(self, variable);
    }
    fn visit_clause_mut(&mut self, clause: &'p mut Clause) {
        super_visit_clause_mut(self, clause);
    }
    fn visit_relation_mut(&mut self, relation: &'p mut Relation) {
        super_visit_relation_mut(self, relation);
    }
    fn visit_only_via_mut(
        &mut self,
        intro: &'p mut VariableIntro,
        op1: &'p mut (Option<Operator>, Vec<VariableIntro>),
        op2: &'p mut (Option<Operator>, Vec<VariableIntro>),
    ) {
        super_visit_only_via_mut(self, intro, op1, op2);
    }
    fn visit_joined_nodes_mut(&mut self, obligation: &'p mut TwoNodeObligation) {
        super_visit_joined_nodes_mut(self, obligation);
    }
    fn visit_clause_intro_mut(&mut self, intro: &'p mut ClauseIntro) {
        super_visit_clause_intro_mut(self, intro);
    }

    fn visit_clause_num_mut(&mut self, _clause_num: &'p mut String) {}
}

pub fn super_visit_policy_mut<'p, V: VisitMut<'p> + ?Sized>(
    visitor: &mut V,
    policy: &'p mut Policy,
) {
    for definition in &mut policy.definitions {
        visitor.visit_definition_mut(definition);
    }
    visitor.visit_ast_node_mut(&mut policy.body);
}

pub fn super_visit_definition_mut<'p, V: VisitMut<'p> + ?Sized>(
    visitor: &mut V,
    definition: &'p mut Definition,
) {
    visitor.visit_variable_mut(&mut definition.variable);
    visitor.visit_variable_intro_mut(&mut definition.declaration);
    if let Some(filter) = &mut definition.filter {
        visitor.visit_ast_node_mut(filter);
    }
}

pub fn super_visit_variable_intro_mut<'p, V: VisitMut<'p> + ?Sized>(
    visitor: &mut V,
    variable: &'p mut VariableIntro,
) {
    visitor.visit_variable_mut(&mut variable.variable);
}

pub fn super_visit_ast_node_mut<'p, V: VisitMut<'p> + ?Sized>(
    visitor: &mut V,
    node: &'p mut ASTNode,
) {
    visitor.visit_clause_num_mut(&mut node.clause_num);
    match &mut node.ty {
        ASTNodeType::Clause(clause) => {
            visitor.visit_clause_mut(clause);
        }
        ASTNodeType::Relation(relation) => {
            visitor.visit_relation_mut(relation);
        }
        ASTNodeType::OnlyVia(intro, op1, op2) => {
            visitor.visit_only_via_mut(intro, op1, op2);
        }
        ASTNodeType::JoinedNodes(obligation) => {
            visitor.visit_joined_nodes_mut(obligation.as_mut());
        }
    }
}

pub fn super_visit_clause_mut<'p, V: VisitMut<'p> + ?Sized>(
    visitor: &mut V,
    clause: &'p mut Clause,
) {
    visitor.visit_clause_intro_mut(&mut clause.intro);
    visitor.visit_ast_node_mut(&mut clause.body);
}

pub fn super_visit_relation_mut<'p, V: VisitMut<'p> + ?Sized>(
    visitor: &mut V,
    relation: &'p mut Relation,
) {
    match relation {
        Relation::Binary {
            left,
            right,
            typ: _,
        } => {
            visitor.visit_variable_mut(left);
            visitor.visit_variable_mut(right);
        }
        Relation::Negation(relation) => visitor.visit_relation_mut(relation),
        Relation::IsMarked(var, _) => visitor.visit_variable_mut(var),
    }
}

pub fn super_visit_only_via_mut<'p, V: VisitMut<'p> + ?Sized>(
    visitor: &mut V,
    intro: &'p mut VariableIntro,
    op1: &'p mut (Option<Operator>, Vec<VariableIntro>),
    op2: &'p mut (Option<Operator>, Vec<VariableIntro>),
) {
    visitor.visit_variable_intro_mut(intro);
    for intro in op1.1.iter_mut().chain(op2.1.iter_mut()) {
        visitor.visit_variable_intro_mut(intro);
    }
}

pub fn super_visit_joined_nodes_mut<'p, V: VisitMut<'p> + ?Sized>(
    visitor: &mut V,
    obligation: &'p mut TwoNodeObligation,
) {
    visitor.visit_ast_node_mut(&mut obligation.src);
    visitor.visit_ast_node_mut(&mut obligation.sink);
}

pub fn super_visit_clause_intro_mut<'p, V: VisitMut<'p> + ?Sized>(
    visitor: &mut V,
    intro: &'p mut ClauseIntro,
) {
    match intro {
        ClauseIntro::ForEach(intro) => visitor.visit_variable_intro_mut(intro),
        ClauseIntro::ThereIs(intro) => visitor.visit_variable_intro_mut(intro),
        ClauseIntro::Conditional(relation) => visitor.visit_relation_mut(relation),
    }
}

#[allow(dead_code)]
pub trait Visit<'p> {
    fn visit_policy(&mut self, policy: &'p Policy) {
        super_visit_policy(self, policy);
    }
    fn visit_definition(&mut self, definition: &'p Definition) {
        super_visit_definition(self, definition);
    }
    fn visit_ast_node(&mut self, node: &'p ASTNode) {
        super_visit_ast_node(self, node);
    }
    fn visit_variable(&mut self, _variable: &'p Variable) {}
    fn visit_variable_intro(&mut self, variable: &'p VariableIntro) {
        super_visit_variable_intro(self, variable);
    }
    fn visit_clause(&mut self, clause: &'p Clause) {
        super_visit_clause(self, clause);
    }
    fn visit_relation(&mut self, relation: &'p Relation) {
        super_visit_relation(self, relation);
    }
    fn visit_only_via(
        &mut self,
        intro: &'p VariableIntro,
        op1: &'p (Option<Operator>, Vec<VariableIntro>),
        op2: &'p (Option<Operator>, Vec<VariableIntro>),
    ) {
        super_visit_only_via(self, intro, op1, op2);
    }
    fn visit_joined_nodes(&mut self, obligation: &'p TwoNodeObligation) {
        super_visit_joined_nodes(self, obligation);
    }
    fn visit_clause_intro(&mut self, intro: &'p ClauseIntro) {
        super_visit_clause_intro(self, intro);
    }

    fn visit_clause_num(&mut self, _clause_num: &'p str) {}
}

pub fn super_visit_policy<'p, V: Visit<'p> + ?Sized>(visitor: &mut V, policy: &'p Policy) {
    for definition in &policy.definitions {
        visitor.visit_definition(definition);
    }
    visitor.visit_ast_node(&policy.body);
}

pub fn super_visit_definition<'p, V: Visit<'p> + ?Sized>(
    visitor: &mut V,
    definition: &'p Definition,
) {
    visitor.visit_variable(&definition.variable);
    visitor.visit_variable_intro(&definition.declaration);
    if let Some(filter) = &definition.filter {
        visitor.visit_ast_node(filter);
    }
}

pub fn super_visit_variable_intro<'p, V: Visit<'p> + ?Sized>(
    visitor: &mut V,
    variable: &'p VariableIntro,
) {
    visitor.visit_variable(&variable.variable);
}

pub fn super_visit_ast_node<'p, V: Visit<'p> + ?Sized>(visitor: &mut V, node: &'p ASTNode) {
    visitor.visit_clause_num(&node.clause_num);
    match &node.ty {
        ASTNodeType::Clause(clause) => {
            visitor.visit_clause(clause);
        }
        ASTNodeType::Relation(relation) => {
            visitor.visit_relation(relation);
        }
        ASTNodeType::OnlyVia(intro, op1, op2) => {
            visitor.visit_only_via(intro, op1, op2);
        }
        ASTNodeType::JoinedNodes(obligation) => {
            visitor.visit_joined_nodes(obligation.as_ref());
        }
    }
}

pub fn super_visit_clause<'p, V: Visit<'p> + ?Sized>(visitor: &mut V, clause: &'p Clause) {
    visitor.visit_clause_intro(&clause.intro);
    visitor.visit_ast_node(&clause.body);
}

pub fn super_visit_relation<'p, V: Visit<'p> + ?Sized>(visitor: &mut V, relation: &'p Relation) {
    match relation {
        Relation::Binary {
            left,
            right,
            typ: _,
        } => {
            visitor.visit_variable(left);
            visitor.visit_variable(right);
        }
        Relation::Negation(relation) => visitor.visit_relation(relation),
        Relation::IsMarked(var, _) => visitor.visit_variable(var),
    }
}

pub fn super_visit_only_via<'p, V: Visit<'p> + ?Sized>(
    visitor: &mut V,
    intro: &'p VariableIntro,
    op1: &'p (Option<Operator>, Vec<VariableIntro>),
    op2: &'p (Option<Operator>, Vec<VariableIntro>),
) {
    visitor.visit_variable_intro(intro);
    for intro in op1.1.iter().chain(op2.1.iter()) {
        visitor.visit_variable_intro(intro);
    }
}

pub fn super_visit_joined_nodes<'p, V: Visit<'p> + ?Sized>(
    visitor: &mut V,
    obligation: &'p TwoNodeObligation,
) {
    visitor.visit_ast_node(&obligation.src);
    visitor.visit_ast_node(&obligation.sink);
}

pub fn super_visit_clause_intro<'p, V: Visit<'p> + ?Sized>(
    visitor: &mut V,
    intro: &'p ClauseIntro,
) {
    match intro {
        ClauseIntro::ForEach(intro) => visitor.visit_variable_intro(intro),
        ClauseIntro::ThereIs(intro) => visitor.visit_variable_intro(intro),
        ClauseIntro::Conditional(relation) => visitor.visit_relation(relation),
    }
}
