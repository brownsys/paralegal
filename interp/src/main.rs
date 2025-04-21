use anyhow::{ensure, Result};
use clap::Parser;
use paralegal_policy::diagnostics::ControllerContext;
use paralegal_policy::paralegal_spdg::{GlobalNode, Identifier};
use paralegal_policy::{
    assert_error, Context, EdgeSelection, GraphLocation, NodeExt, NodeQueries, SPDGGenCommand,
};
use parsers::{
    parse, ASTNode, Binop, Clause, ClauseIntro, Definition, DefinitionScope, Operator, Policy,
    PolicyScope, Relation, VariableIntro, VariableIntroType,
};
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub enum Value {
    Type,
    Node(GlobalNode),
    Set(HashSet<GlobalNode>),
}

impl Value {
    fn into_node(&self) -> Option<GlobalNode> {
        match self {
            Value::Node(n) => Some(*n),
            _ => None,
        }
    }

    fn expect_node(&self) -> GlobalNode {
        self.into_node()
            .unwrap_or_else(|| panic!("Expected node, got {:?}", self))
    }
}

struct Interpreter<'p> {
    policy: &'p Policy,
    context: Arc<ControllerContext>,
    var_stack: HashMap<&'p str, Value>,
}

impl<'p> Interpreter<'p> {
    fn new(policy: &'p Policy, context: Arc<ControllerContext>) -> Self {
        Self {
            policy,
            context,
            var_stack: HashMap::new(),
        }
    }

    fn variable_intro_nodes(&self, intro_type: &VariableIntroType) -> HashSet<GlobalNode> {
        match intro_type {
            VariableIntroType::AllNodes => self.context.all_nodes().collect(),
            VariableIntroType::Roots => unimplemented!(),
            VariableIntroType::Variable => unimplemented!(),
            VariableIntroType::VariableMarked { marker, on_type } => {
                if *on_type {
                    self.context
                        .nodes_marked_via_type(Identifier::new_intern(marker))
                        .collect()
                } else {
                    self.context
                        .marked_nodes(Identifier::new_intern(marker))
                        .collect()
                }
            }
            VariableIntroType::VariableSourceOf(_) => unimplemented!(),
        }
    }

    fn run(&mut self) -> Result<bool> {
        self.handle_definitions(&self.policy.definitions);

        Ok(self.run_filter(&self.policy.body))
    }

    fn handle_definitions(&mut self, definitions: &'p [Definition]) {
        for d in definitions {
            self.handle_definition(d)
        }
    }

    fn evaluate_var_intro_as_set(
        &mut self,
        intro: &'p VariableIntro,
        filter: Option<&'p ASTNode>,
    ) -> HashSet<GlobalNode> {
        let mut results = HashSet::new();
        let target_var = intro.variable.as_str();
        self.with_declaration(intro, |slf| {
            let matches_filter = filter.is_none_or(|f| slf.run_filter(f));
            if matches_filter {
                results.insert(slf.lookup(target_var).unwrap().into_node().unwrap());
            }
            true
        });
        results
    }

    fn handle_definition(&mut self, definition: &'p Definition) {
        assert!(matches!(definition.scope, DefinitionScope::Everywhere));
        let results =
            self.evaluate_var_intro_as_set(&definition.declaration, Some(&definition.filter));
        self.define(&definition.variable, Value::Set(results));
    }

    fn run_filter(&mut self, filter: &'p ASTNode) -> bool {
        match filter {
            ASTNode::Relation(rel) => self.evaluate_relation(rel),
            ASTNode::OnlyVia(var_intro, (mid_op, mid), (end_op, end)) => {
                let start_set = self.evaluate_var_intro_as_set(var_intro, None);
                assert!(mid_op.is_none());
                assert!(end_op.is_none());
                assert_eq!(mid.len(), 1);
                assert_eq!(end.len(), 1);
                let mid = self.evaluate_var_intro_as_set(&mid[0], None);
                let end = self.evaluate_var_intro_as_set(&end[0], None);
                self.context
                    .always_happens_before(start_set, |n| mid.contains(&n), |n| end.contains(&n))
                    .unwrap()
                    .holds()
            }
            ASTNode::Clause(cls) => self.run_clause(cls),
            ASTNode::JoinedNodes(obl) => {
                let left = self.run_filter(&obl.src);
                if matches!(
                    (&obl.op, left),
                    (Operator::And, false) | (Operator::Or, true)
                ) {
                    return left;
                }
                let right = self.run_filter(&obl.sink);
                match obl.op {
                    Operator::And => left & right,
                    Operator::Or => left | right,
                }
            }
        }
    }

    fn run_clause(&mut self, clause: &'p Clause) -> bool {
        let (intro, mut fail_fast_on, result) = match &clause.intro {
            ClauseIntro::Conditional(_) => unimplemented!(),
            ClauseIntro::ForEach(intro) => (intro, false, true),
            ClauseIntro::ThereIs(intro) => (intro, true, false),
        };

        self.with_declaration(intro, |slf| {
            let filter_result = slf.run_filter(&clause.body);
            fail_fast_on ^= filter_result;
            fail_fast_on
        });
        fail_fast_on == result
    }

    fn evaluate_relation(&self, relation: &Relation) -> bool {
        match relation {
            Relation::IsMarked(node, marker) => {
                let node = self.lookup(node).unwrap().into_node().unwrap();
                node.has_marker(&self.context, Identifier::new_intern(marker))
            }
            Relation::Binary { left, right, typ } => {
                let left = self.expect_lookup(left).expect_node();
                let right = self.expect_lookup(right).expect_node();
                let edge_type = match typ {
                    Binop::AssociatedCallSite => {
                        unimplemented!()
                    }
                    Binop::Both => EdgeSelection::Both,
                    Binop::Control => EdgeSelection::Control,
                    Binop::Data => EdgeSelection::Data,
                };

                left.flows_to(right, &self.context, edge_type)
            }
            Relation::Negation(inner) => !self.evaluate_relation(inner),
        }
    }

    fn with_declaration(
        &mut self,
        declaration: &'p VariableIntro,
        mut f: impl FnMut(&mut Self) -> bool,
    ) {
        let name = declaration.variable.as_str();
        let values = self.variable_intro_nodes(&declaration.intro);
        let old = self.var_stack.remove(name);
        for value in values {
            let cont = self.with_scoped_var(name, Value::Node(value), |slf| f(slf));

            if !cont {
                break;
            }
        }
        if let Some(old) = old {
            self.var_stack.insert(name, old);
        }
    }

    fn define(&mut self, name: &'p str, value: Value) {
        self.var_stack.insert(name, value);
    }

    fn lookup(&self, name: &'p str) -> Option<&Value> {
        self.var_stack.get(name)
    }

    fn expect_lookup(&self, name: &'p str) -> &Value {
        self.var_stack
            .get(name)
            .unwrap_or_else(|| panic!("Variable {name} not found"))
    }

    fn with_scoped_var<R>(
        &mut self,
        name: &'p str,
        value: Value,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let old = self.var_stack.insert(name, value);
        let result = f(self);
        if let Some(old) = old {
            self.var_stack.insert(name, old);
        } else {
            self.var_stack.remove(name);
        }
        result
    }
}

fn interp(policy: &Policy, ctx: Arc<Context>) -> Result<bool> {
    for ctx in ctx.controller_contexts() {
        if matches!(&policy.scope, PolicyScope::InCtrler(c) if c != ctx.current().name.as_str()) {
            continue;
        }
        let mut i = Interpreter::new(policy, ctx);
        let success = i.run()?;
        match &policy.scope {
            PolicyScope::Somewhere if success => return Ok(true),
            PolicyScope::Everywhere if !success => return Ok(false),
            PolicyScope::InCtrler(_) if success => return Ok(true),
            _ => todo!(),
        }
    }
    Ok(matches!(policy.scope, PolicyScope::Everywhere))
}

#[derive(Parser)]
struct Args {
    file: PathBuf,
    #[clap(long)]
    no_pdg_gen: bool,
    #[clap(long, default_value = ".")]
    crate_path: PathBuf,
    #[clap(last = true)]
    flow_args: Vec<String>,
}

fn main() -> Result<()> {
    let args = Args::parse();

    let policy_file = std::fs::read_to_string(args.file)?;

    let (s, policy) = parse(&policy_file).unwrap();

    assert!(s.is_empty());

    let graph_loc = if !args.no_pdg_gen {
        SPDGGenCommand::global().run(args.crate_path)?
    } else {
        GraphLocation::std(args.crate_path)
    };

    let result = graph_loc.with_context(|ctx| {
        let interp_result = interp(&policy, ctx.clone())?;
        assert_error!(ctx, interp_result, "Policy failed");
        Ok(())
    })?;

    ensure!(result.success, "Policy failed");

    Ok(())
}
