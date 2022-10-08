#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;
use dfpp::Symbol;

extern crate rustc_middle;
extern crate rustc_span;
use rustc_middle::mir;

const CRATE_LOC_VAR: &'static str = "DFPP_EXAMPLE_CRATE";

lazy_static! {
    static ref EXAMPLE_CRATE_LOC: std::path::PathBuf = std::env::var(CRATE_LOC_VAR)
        .unwrap_or_else(|_| panic!("Please set the {CRATE_LOC_VAR} env variable to the location of the `dfpp-examples` repo."))
        .into();
}

fn with_current_directory<P: AsRef<std::path::Path>, A, F: FnOnce() -> A>(
    p: P,
    f: F,
) -> std::io::Result<A> {
    let current = std::env::current_dir()?;
    std::env::set_current_dir(p)?;
    let res = f();
    std::env::set_current_dir(current)?;
    Ok(res)
}

fn cwd_and_use_rustc_in<P: AsRef<std::path::Path>, A, F: FnOnce() -> A>(
    p: P,
    f: F,
) -> std::io::Result<A> {
    with_current_directory(p, || {
        rustc_span::create_default_session_if_not_set_then(|_| f())
    })
}

fn example_crate_loc(name: &str) -> std::path::PathBuf {
    let mut b = EXAMPLE_CRATE_LOC.to_path_buf();
    b.push(name);
    b
}

fn compile_example_crate() {
    assert!(std::process::Command::new("cargo")
        .arg("dfpp")
        .arg("--dump-serialized-non-transitive-graph")
        .status()
        .unwrap()
        .success())
}

type SimpleMirBody = Vec<(mir::Location, String)>;

fn function_call(body: &SimpleMirBody, pattern: &str) -> mir::Location {
    body.iter()
        .find(|(_, s)| s.contains(pattern))
        .unwrap_or_else(|| panic!("Pattern {pattern} not found in {body:?}"))
        .0
}

use dfpp::foreign_serializers::SerializableNonTransitiveGraph;

fn connects(g: &SerializableNonTransitiveGraph, from: mir::Location, to: mir::Location) -> bool {
    let mut queue = vec![to];
    while let Some(n) = queue.pop() {
        if n == from {
            return true;
        }
        g[&n]
            .rows()
            .map(|p| p.1)
            .for_each(|s| queue.extend(s.iter()))
    }
    false
}

fn connects_direct(g: &SerializableNonTransitiveGraph, from: mir::Location, to: mir::Location) -> bool {
    g[&to].rows().any(|(_, r)| r.iter().any(|i| i == &from))
}

#[test]
fn simple_happens_before_has_connections() {
    let (ref body, ref graph) =
        cwd_and_use_rustc_in(example_crate_loc("happens-before-basic"), || {
            compile_example_crate();
            dfpp::dbg::read_non_transitive_graph_and_body(Symbol::intern("process_user_data"))
        })
        .unwrap();

    eprintln!("Deser done.");

    assert!(connects(
        graph,
        function_call(body, "get_user_data"),
        function_call(body, "dp_user_data")
    ));
    assert!(connects(
        graph,
        function_call(body, "dp_user_data"),
        function_call(body, "send_user_data")
    ));
    assert!(connects(
        graph,
        function_call(body, "get_user_data"),
        function_call(body, "send_user_data")
    ));
}

#[test]
fn happens_before_if_has_connections() {
    let (ref body, ref graph) =
        cwd_and_use_rustc_in(example_crate_loc("happens-before-if"), || {
            compile_example_crate();
            dfpp::dbg::read_non_transitive_graph_and_body(Symbol::intern("process_user_data"))
        })
        .unwrap();
    eprintln!("Deser done.");
    assert!(connects(
        graph,
        function_call(body, "get_user_data"),
        function_call(body, "dp_user_data")
    ));
    assert!(connects(
        graph,
        function_call(body, "dp_user_data"),
        function_call(body, "send_user_data")
    ));
    assert!(connects_direct(
        graph,
        function_call(body, "get_user_data"),
        function_call(body, "send_user_data")
    ));
}
