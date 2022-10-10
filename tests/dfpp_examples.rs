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

use dfpp::foreign_serializers::SerializableNonTransitiveGraph;

struct G {
    graph: SerializableNonTransitiveGraph,
    body: SimpleMirBody,
}

impl G {
    fn connects(&self, from: mir::Location, to: mir::Location) -> bool {
        let mut queue = vec![to];
        while let Some(n) = queue.pop() {
            if n == from {
                return true;
            }
            self.graph[&n]
                .rows()
                .map(|p| p.1)
                .for_each(|s| queue.extend(s.iter()))
        }
        false
    }
    fn connects_direct(&self, from: mir::Location, to: mir::Location) -> bool {
        self.graph[&to]
            .rows()
            .any(|(_, r)| r.iter().any(|i| i == &from))
    }

    fn function_call(&self, pattern: &str) -> mir::Location {
        self.body
            .iter()
            .find(|(_, s)| s.contains(pattern))
            .unwrap_or_else(|| panic!("Pattern {pattern} not found in {:?}", self.body))
            .0
    }
    fn from_file(s: Symbol) -> Self {
        let (body, graph) = dfpp::dbg::read_non_transitive_graph_and_body(s);
        Self { graph, body }
    }
}

#[test]
fn simple_happens_before_has_connections() {
    let graph = cwd_and_use_rustc_in(example_crate_loc("happens-before-basic"), || {
        compile_example_crate();
        G::from_file(Symbol::intern("process_user_data"))
    })
    .unwrap();

    let get = graph.function_call("get_user_data");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(get, dp));
    assert!(graph.connects(dp, send));
    assert!(graph.connects(get, send));
    assert!(!graph.connects_direct(get, send))
}

#[test]
fn happens_before_if_has_connections() {
    let graph = cwd_and_use_rustc_in(example_crate_loc("happens-before-if"), || {
        compile_example_crate();
        G::from_file(Symbol::intern("process_user_data"))
    })
    .unwrap();

    let get = graph.function_call("get_user_data");
    let dp = graph.function_call("dp_user_data");
    let send = graph.function_call("send_user_data");
    assert!(graph.connects(get, dp,));
    assert!(graph.connects(dp, send));
    assert!(graph.connects_direct(get, send));
}
