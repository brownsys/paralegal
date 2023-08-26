use crate::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

/// Coarse grained, [`Place`](mir::Place) abstracted version of a
/// [`GlobalFlowGraph`].
#[derive(Serialize, Deserialize)]
#[serde(bound(
    serialize = "Location: std::cmp::Eq + std::hash::Hash + serde::Serialize",
    deserialize = "Location: std::cmp::Eq + std::hash::Hash + serde::Deserialize<'de>"
))]
pub struct CallOnlyFlow<Location> {
    #[serde(with = "crate::serializers::serde_map_via_vec")]
    pub location_dependencies: HashMap<Location, CallDeps<Location>>,
    pub return_dependencies: HashSet<Location>,
}

/// Dependencies of a function call with the [`Place`](mir::Place)s abstracted
/// away. Instead each location in the `input_deps` vector corresponds to the
/// dependencies for the positional argument at that index. For methods the 0th
/// index is `self`.
#[derive(serde::Serialize, serde::Deserialize)]
#[serde(bound(
    serialize = "Location: std::cmp::Eq + std::hash::Hash + serde::Serialize",
    deserialize = "Location: std::cmp::Eq + std::hash::Hash + serde::Deserialize<'de>"
))]
pub struct CallDeps<Location> {
    /// Additional dependencies that arise from the control flow, e.g. the scope
    /// this function call is located in.
    pub ctrl_deps: HashSet<Location>,
    /// Dependencies of each argument in the same order as the parameters
    /// provided to the function call.
    pub input_deps: Vec<HashSet<Location>>,
}
