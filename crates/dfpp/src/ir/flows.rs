use crate::{ir::GlobalLocation, HashMap, HashSet};

use serde::{Deserialize, Serialize};

/// Coarse grained, [`Place`](mir::Place) abstracted version of a
/// [`GlobalFlowGraph`].
#[derive(Serialize, Deserialize)]
pub struct CallOnlyFlow {
    pub location_dependencies: HashMap<GlobalLocation, CallDeps>,
    pub return_dependencies: HashSet<GlobalLocation>,
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

/// Dependencies of a function call with the [`Place`](mir::Place)s abstracted
/// away. Instead each location in the `input_deps` vector corresponds to the
/// dependencies for the positional argument at that index. For methods the 0th
/// index is `self`.
#[derive(Serialize, Deserialize)]
pub struct CallDeps {
    /// Additional dependencies that arise from the control flow, e.g. the scope
    /// this function call is located in.
    pub ctrl_deps: HashSet<GlobalLocation>,
    /// Dependencies of each argument in the same order as the parameters
    /// provided to the function call.
    pub input_deps: Vec<HashSet<GlobalLocation>>,
}
