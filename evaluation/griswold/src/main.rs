use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::time::Duration;

struct Run {
    compilation: &'static [&'static str],
    policies: fn(Arc<Context>) -> Result<()>,
}

#[derive(Serialize, Deserialize)]
struct RunResult {
    id: u32,
    run_id: u32,
    experiment: &'static str,
    policy: &'static str,
    expectation: bool,
    result: bool,
    pdg_time: Duration,
    rustc_time: Duration,
    flowistry_time: Duration,
    conversion_time: Duration,
    serialization_time: Duration,
    policy_time: Duration,
    derialization_time: Duration,
    precomputation_time: Duration,
    traversal_time: Duration,
    num_nodes: u32,
    num_controllers: u16,
    unique_locs: u32,
    unique_functions: u32,
    analyzed_locs: u32,
    analyzed_function: u32,
    inlinings_performed: u32,
    max_inlining_depth: u16,
}

fn main() {
    println!("Hello, world!");
}
