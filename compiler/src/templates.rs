use std::collections::HashMap;

use handlebars::Handlebars;
use parsers::{VariableIntro, ASTNode, Relation, Operator, PolicyScope};

const PATH_PREFIX : &str = "templates/";
const PATH_SUFFIX : &str = ".handlebars";
const BASE : &str = "base"; // all policies use base; has infrastructure to set up and run policy

pub fn register(handlebars: &mut Handlebars) {
    for (name, path) in TEMPLATES {
        handlebars
        .register_template_file(name, path)
        .expect(&format!(
            "Could not register {name} template with handlebars"
        ));
    }
}

pub fn render<'a>(
    handlebars: &mut Handlebars,
    map: &HashMap<&str, &str>,
    name: &'a str,
) -> String {
    handlebars
        .render(name, &map)
        .expect(&format!("Could not render {name} handlebars template"))
}

/*

for variable marked, template to get all nodes marked marker and name it var
for variable of type marked, template to get all types marked marker and name it var
for variable source of, template to get all sources of type_var and name it var

*/
