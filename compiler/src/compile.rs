use handlebars::{no_escape, Handlebars};
use serde::Serialize;
use std::collections::HashMap;
use std::fs;
use std::io::Result;

const BASE_TEMPLATE: &str = "base";
const ALWAYS_TEMPLATE: &str = "always";
const SOMETIMES_TEMPLATE: &str = "sometimes";
const ALL_VAR_INTRO_TEMPLATE: &str = "all-var-intro";
const SOME_VAR_INTRO_TEMPLATE: &str = "some-var-intro";
const FLOWS_TO_TEMPLATE: &str = "flows-to";
const CONTROL_FLOW_TEMPLATE: &str = "control-flow";
const THROUGH_TEMPLATE: &str = "through";
const IMPLIES_TEMPLATE: &str = "implies";
const AND_TEMPLATE: &str = "and";
const OR_TEMPLATE: &str = "or";
const NODES_TEMPLATE: &str = "nodes";

/* TODOs
    (Functionality)
    - For "a flows to b", instead of getting every node marked b, then filtering
      for the ones that a flows to, call influencees to start from what a flows to
      and filter to the ones marked b.
    - conditionals: have multiples? perhaps only allowed after periods.
    - parentheses to change order that obligations are enforced (e.g., A and (B or C)))
    - add "In <controller name>" in addition to Always/Sometimes, meaning Paralegal should apply
      the policy to the controller with that name
    - unbound variable errors (variables referenced in bodies that weren't declared)
    - “is authorized by” primitive as syntactic sugar
    - possible syntactic sugar for flows to / control flow influence
    - negation : "no quantifier" / "does not flow to"
    - "one" quantifier
    - figure out which edge type "flows to" compiles to or if the grammar should let you specify

    (Good Practice / User Experience / Nits)
    - better error handling
    - pass template file paths as arguments instead of string literals
    - escaping {{}} in Rust code w/o overwriting no-escape for HTML characters
    - better leveraging of handlebars functionality (partials)
    - cargo new for the policy and write a template a Cargo.toml for it as well
    - better separate concerns in this repository (break up parsers into multiple files, etc.)
*/

// fn func_call(q: &Quantifier) -> &str {
//     match q {
//         Quantifier::Some => "any",
//         Quantifier::All => "all",
//         // Quantifier::No => todo!(),
//     }
// }

fn node_to_template<'a>(node: &'a ASTNode<'a>) -> &'a str {
    match node {
        ASTNode::FlowsTo(_) => FLOWS_TO_TEMPLATE,
        ASTNode::ControlFlow(_) => CONTROL_FLOW_TEMPLATE,
        ASTNode::OnlyVia(_) => THROUGH_TEMPLATE,
        ASTNode::And(_) => AND_TEMPLATE,
        ASTNode::Or(_) => OR_TEMPLATE,
        // ASTNode::Implies(_) => IMPLIES_TEMPLATE,
        ASTNode::VarIntroduction(ob) => {
            match ob.binding.quantifier {
                Quantifier::All => ALL_VAR_INTRO_TEMPLATE,
                Quantifier::Some => SOME_VAR_INTRO_TEMPLATE,
            }
        }
    }
}

fn scope_to_template(scope : &PolicyScope) -> &str {
    match scope {
        PolicyScope::Always => ALWAYS_TEMPLATE,
        PolicyScope::Sometimes => SOMETIMES_TEMPLATE
    }
}

fn register_templates(handlebars: &mut Handlebars) {
    let templates: Vec<(&str, &str)> = Vec::from([
        (BASE_TEMPLATE, "templates/policy.handlebars"),
        (ALL_VAR_INTRO_TEMPLATE, "templates/astnodes/all-intro.handlebars"),
        (SOME_VAR_INTRO_TEMPLATE, "templates/astnodes/some-intro.handlebars"),
        (FLOWS_TO_TEMPLATE, "templates/astnodes/flows-to.handlebars"),
        (CONTROL_FLOW_TEMPLATE, "templates/astnodes/control-flow.handlebars"),
        (THROUGH_TEMPLATE, "templates/astnodes/through.handlebars"),
        (AND_TEMPLATE, "templates/astnodes/and.handlebars"),
        (OR_TEMPLATE, "templates/astnodes/or.handlebars"),
        (IMPLIES_TEMPLATE, "templates/astnodes/implies.handlebars"),
        (ALWAYS_TEMPLATE, "templates/scope/always.handlebars"),
        (SOMETIMES_TEMPLATE, "templates/scope/sometimes.handlebars"),
        (NODES_TEMPLATE, "templates/nodes.handlebars")
    ]);
    
    for (name, path) in templates {
        handlebars
        .register_template_file(name, path)
        .expect(&format!(
            "Could not register {name} template with handlebars"
        ));
    }
}

fn render_template<'a, T: serde::Serialize, U: serde::Serialize>(
    handlebars: &mut Handlebars,
    map: &HashMap<T, U>,
    name: &'a str,
) -> String {
    handlebars
        .render(name, &map)
        .expect(&format!("Could not render {name} handlebars template"))
}

fn verify_vars_in_scope<'a>(vars : Vec<&Variable<'a>>, env : &HashMap<Variable<'a>, Marker<'a>>) {
    for var in vars {
        if !env.contains_key(var) {
            let msg = format!("Cannot reference variable {}; it has not been introduced", {var});
            panic!("{}", msg);
        }
    }
}

fn traverse_ast<'a>(
    handlebars: &mut Handlebars,
    node: &ASTNode<'a>,
    env: &mut HashMap<Variable<'a>, Marker<'a>>
) -> String {
    let mut map: HashMap<&str, &str> = HashMap::new();
    match node {
        ASTNode::FlowsTo(obligation) | ASTNode::ControlFlow(obligation)  => {
            verify_vars_in_scope(vec![&obligation.src, &obligation.dest], &env);
            map.insert("src", obligation.src);
            map.insert("dest", obligation.dest);
            render_template(handlebars, &map, node_to_template(&node))
        },
        ASTNode::OnlyVia(obligation) => {
            verify_vars_in_scope(vec![&obligation.src, &obligation.dest, &obligation.checkpoint], &env);
            // come back to this, depends on quantifier
            todo!()
        },
        ASTNode::And(obligation) | ASTNode::Or(obligation) | ASTNode::Implies(obligation) => {
            let src_res = &traverse_ast(handlebars, &obligation.src, env);
            map.insert("src", src_res);
            let dest_res = &traverse_ast(handlebars, &obligation.dest, env);
            map.insert("dest", dest_res);
            render_template(handlebars, &map, node_to_template(&node))
        },
        ASTNode::VarIntroduction(clause) => {
            if env.contains_key(clause.binding.variable) {
                panic!("Policy already introduced this variable; choose a different name");
            }
            env.insert(clause.binding.variable, clause.binding.marker);

            let res = &traverse_ast(handlebars, &clause.body, env);
            map.insert("variable", clause.binding.variable);
            map.insert("body", res);

            // if the variable clause closes, the variable is now out of scope, so remove it from the environment
            env.remove(clause.binding.variable);

            render_template(handlebars, &map, node_to_template(&node))
        }
    }
}

fn compile_policy<'a>(
    handlebars: &mut Handlebars,
    policy: Policy<'a>,
) -> Result<()> {
    let mut env: HashMap<Variable<'a>, Marker<'a>> = HashMap::new();
    let obligation = traverse_ast(handlebars, &policy.body, &mut env);
    
    let mut nodes_map: HashMap<&str, HashMap<Variable<'a>, Marker<'a>>> = HashMap::new();
    // TODO not sure if this is going to work or if env needs to be a list
    nodes_map.insert("bindings", env);
    let nodes = render_template(handlebars, &nodes_map, NODES_TEMPLATE);

    let mut map: HashMap<&str, &str> = HashMap::new();
    map.insert("nodes", &nodes);
    map.insert("obligation", &obligation);
    let policy_logic = render_template(handlebars, &map, scope_to_template(&policy.scope));
    map.clear();

    map.insert("policy", &policy_logic);
    let res = render_template(handlebars, &map, BASE_TEMPLATE);

    fs::write("compiled-policy.rs", &res)?;
    Ok(())
}

pub fn compile<'a>(policy: Policy<'a>) -> Result<()> {
    let mut handlebars = Handlebars::new();
    handlebars.register_escape_fn(no_escape);
    register_templates(&mut handlebars);
    compile_policy(&mut handlebars, policy)
}
