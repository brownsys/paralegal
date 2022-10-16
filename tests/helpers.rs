#![feature(rustc_private)]
extern crate rustc_middle;
extern crate rustc_span;
use dfpp::{HashSet, Symbol};
use rustc_middle::mir;

pub fn with_current_directory<
    P: AsRef<std::path::Path>,
    A,
    F: std::panic::UnwindSafe + FnOnce() -> A,
>(
    p: P,
    f: F,
) -> std::io::Result<A> {
    let current = std::env::current_dir()?;
    std::env::set_current_dir(p)?;
    let res = std::panic::catch_unwind(f);
    std::env::set_current_dir(current)?;
    match res {
        Ok(r) => Ok(r),
        Err(e) => std::panic::resume_unwind(e),
    }
}

pub fn cwd_and_use_rustc_in<
    P: AsRef<std::path::Path>,
    A,
    F: std::panic::UnwindSafe + FnOnce() -> A,
>(
    p: P,
    f: F,
) -> std::io::Result<A> {
    with_current_directory(p, || {
        rustc_span::create_default_session_if_not_set_then(|_| f())
    })
}

pub fn install_dfpp() -> bool {
    std::process::Command::new("cargo")
        .arg("install")
        .arg("--locked")
        .arg("--offline")
        .arg("--path")
        .arg(".")
        .arg("--debug")
        .status()
        .unwrap()
        .success()
}

pub fn run_dfpp_with_graph_dump() -> bool {
    std::process::Command::new("cargo")
        .arg("dfpp")
        .arg("--use-non-transitive-graph")
        .arg("--dump-serialized-non-transitive-graph")
        .arg("--shrink-flow-domains")
        .status()
        .unwrap()
        .success()
}

pub type SimpleMirBody = Vec<(mir::Location, String, HashSet<Symbol>)>;

use dfpp::foreign_serializers::SerializableNonTransitiveGraph;

pub struct G {
    pub graph: SerializableNonTransitiveGraph,
    pub body: SimpleMirBody,
}

impl G {
    fn predecessors(&self, n: mir::Location) -> impl Iterator<Item = &mir::Location> {
        self.graph.get(&n).into_iter().flat_map(move |r| {
            self.body
                .iter()
                .find(|t| t.0 == n)
                .unwrap()
                .2
                .iter()
                .flat_map(|p| r.row(*p))
        })
    }
    pub fn connects(&self, from: mir::Location, to: mir::Location) -> bool {
        let mut queue = vec![to];
        let mut seen = HashSet::new();
        while let Some(n) = queue.pop() {
            if seen.contains(&n) {
                continue;
            } else {
                seen.insert(n);
            }
            if n == from {
                return true;
            }
            queue.extend(self.predecessors(n))
        }
        false
    }
    pub fn connects_direct(&self, from: mir::Location, to: mir::Location) -> bool {
        self.predecessors(to).any(|l| *l == from)
    }

    pub fn function_call(&self, pattern: &str) -> mir::Location {
        self.body
            .iter()
            .find(|(_, s, _)| s.contains(pattern))
            .unwrap_or_else(|| panic!("Pattern {pattern} not found in {:?}", self.body))
            .0
    }
    pub fn from_file(s: Symbol) -> Self {
        let (body, graph) = dfpp::dbg::read_non_transitive_graph_and_body(s);
        Self { graph, body }
    }
    pub fn argument(&self, n: usize) -> mir::Location {
        self.body
            .iter()
            .find(|(_, s, _)| s == format!("Argument _{n}").as_str())
            .unwrap_or_else(|| panic!("Argument {n} not found in {:?}", self.body))
            .0
    }
}
