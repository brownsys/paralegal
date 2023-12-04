use flowistry::pdg;
use pdg::graph::{DepGraph, CallString, GlobalLocation};
use petgraph::EdgeDirection;
use crate::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

/// Coarse grained, [`Place`](mir::Place) abstracted version of a
/// [`GlobalFlowGraph`].
#[derive(Serialize, Deserialize)]
pub struct CallOnlyFlow {
    pub location_dependencies: HashMap<CallString, CallDeps>,
    pub return_dependencies: HashSet<CallString>,
}

impl CallOnlyFlow {
    pub fn all_locations_iter(&self) -> impl Iterator<Item = &GlobalLocation> + '_ {
        self.location_dependencies.iter().flat_map(|(from, deps)| {
            std::iter::once(from).chain(
                std::iter::once(&deps.ctrl_deps)
                    .chain(deps.input_deps.iter())
                    .flatten(),
            )
        })
    }
}

impl From<&'_ DepGraph> for CallOnlyFlow {
    fn from(value: &DepGraph) -> Self {
        use petgraph::prelude::*;
        use flowistry::pdg::graph::*;
        let g = &value.graph;
        let mut return_dependencies = None;
        let location_dependencies = g.node_indices()
            .filter_map(|i| {
                let n = g.node_weight(i)?;

                if n.place == mir::RETURN_PLACE && n.at.len() == 0 {
                    assert!(return_dependencies.replace(
                        g.neighbors_directed(i, Incoming).map(|p|
                            g.node_weight(p).unwrap().at
                        ).collect()
                    ).is_none());
                    None
                } else {
                    let mut input_deps = vec![];
                    let mut ctrl_deps = HashSet::new();
                    for e_ref in g.edges_directed(i, Incoming) {
                        let dep= g.node_weight(e_ref.source()).unwrap().at;
                        match e_ref.weight().kind {
                            DepEdgeKind::Control => {
                                ctrl_deps.insert(dep);
                            },
                            DepEdgeKind::Data => {
                                let arg_num = 0_usize;
                                if input_deps.len() <= arg_num {
                                    input_deps.resize_with(arg_num, HashSet::new);
                                }
                                input_deps[arg_num].insert(dep);
                            }
                        }
                    }
                    Some((n.at, CallDeps { ctrl_deps, input_deps }))
                }
            })
            .collect();

        CallOnlyFlow {
            location_dependencies,
            return_dependencies: return_dependencies.unwrap()
        }

    }
}

/// Dependencies of a function call with the [`Place`](mir::Place)s abstracted
/// away. Instead each location in the `input_deps` vector corresponds to the
/// dependencies for the positional argument at that index. For methods the 0th
/// index is `self`.
#[derive(Serialize, Deserialize)]
pub struct CallDeps {
    /// Additional dependencies that arise from the control flow, e.g. the scope
    /// this function call is located in.
    pub ctrl_deps: HashSet<CallString>,
    /// Dependencies of each argument in the same order as the parameters
    /// provided to the function call.
    pub input_deps: Vec<HashSet<CallString>>,
}
