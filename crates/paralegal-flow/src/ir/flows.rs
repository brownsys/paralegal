use petgraph::data::DataMap;
use petgraph::graph::NodeIndex;
use petgraph::visit::{Data, depth_first_search, DfsEvent, EdgeFiltered, EdgeFilteredEdges, GraphBase, Reversed};
use crate::{HashMap, HashSet, mir, pdg::*, Either, TyCtxt, utils::{TyCtxtExt, AsFnAndArgs}};
use serde::{Deserialize, Serialize};

/// Coarse grained, [`Place`](mir::Place) abstracted version of a
/// [`GlobalFlowGraph`].
#[derive(Serialize, Deserialize)]
pub struct CallOnlyFlow {
    pub location_dependencies: HashMap<CallString, CallDeps>,
    pub return_dependencies: HashSet<CallString>,
}

impl CallOnlyFlow {
    pub fn all_locations_iter(&self) -> impl Iterator<Item = &CallString> + '_ {
        self.location_dependencies.iter().flat_map(|(from, deps)| {
            std::iter::once(from).chain(
                std::iter::once(&deps.ctrl_deps)
                    .chain(deps.input_deps.iter())
                    .flatten(),
            )
        })
    }
}

enum DependencyResult {
    IsReturn(HashSet<CallString>),
    IsCall {
        node: CallString,
        deps: CallDeps,
    },
    Skip,
}

fn arg_nums_for_dep<'tcx>(tcx: TyCtxt<'tcx>, place: mir::Place<'tcx>, location: CallString) -> Vec<usize> {
    let location = location.leaf();
    let body = &tcx.body_for_def_id(location.function.to_def_id()).unwrap().body;
    let stmt = body.stmt_at(location.location.unwrap_location());
    let Either::Right(terminator) = stmt else {
        unreachable!("{stmt:?} is not a terminator")
    };
    let args = terminator.as_fn_and_args(tcx).unwrap().1;
    args.iter().enumerate().filter_map(|(num, &op)| (op? == place).then_some(num)).collect()
}

fn is_statement(tcx: TyCtxt, location: GlobalLocation) -> bool {
}

fn search_ancestors<G, I, F>(tcx: TyCtxt, g: G, start: I, found: impl FnMut(NodeIndex))
where
    G: petgraph::visit::IntoNeighbors + petgraph::visit::Visitable,
    I: IntoIterator<Item = G::NodeId>,
    G: GraphBase<NodeId=NodeIndex> + Data<NodeWeight=DepNode, EdgeWeight=DepEdge>
{
    use petgraph::visit::{depth_first_search, DfsEvent, Control};
    // The dfs later uses "into_neighbors" which for a directed graph normally returns all outgoing
    // edges but we want to traverse the other direction so we reverse all edge direction. Now the
    // DFS will traverse towards the ancestors.
    //
    // In addition we filter out the control flow edges. This is because this function is used in
    // two contexts, both of which are save to ignore control.
    // XXX: Check these assumptions with test cases
    //
    // 1. We are discovering the data dependencies to a function call, in this case we don't care
    //    about the control flow.
    // 2. For the control flow reaching a call site we care about the pattern
    //    "n_1 ->{data}* n_2 ->{ctrl} target", ergo only the last edge has to be control but the
    //    rest is data only. The rest is data only, because the control flow edges contain
    //    transitive edges already, allowing us to ignore them here.
    let g = Reversed(EdgeFiltered::from_fn(g, |e| matches!(e.weight().kind, DepEdgeKind::Data)));
    depth_first_search(
        g,
        start,
        |event| match event {
            DfsEvent::Discover(node, _) =>
                if is_statement(tcx, g.node_weight(node).unwrap().at.leaf()) {
                    Control::Continue
                } else {
                    found(node);
                    Control::Prune
                }
            _ => Control::Continue,
        }
    );
}

fn dependencies_of_node<'tcx>(tcx: TyCtxt<'tcx>, g: &DepGraph<'tcx>, i: NodeIndex) -> DependencyResult {
    use petgraph::prelude::*;
    let g = &g.graph;
    let n = g.node_weight(i).unwrap();

    if n.place == mir::RETURN_PLACE.into() && n.at.iter().count() == 0
    {
        DependencyResult::IsReturn(
            g.neighbors_directed(i, Incoming)
                .map(|p| g.node_weight(p).unwrap().at)
                .collect()
        )
    } else {
        use petgraph::visit::{depth_first_search, DfsEvent, Control};
        let mut input_deps = vec![];
        let mut ctrl_deps = HashSet::new();

        // We don't need to worry about transitive ctrl edges, because they're already included?

        search_ancestors(tcx, g, |ancestor| {

        });

        for e_ref in g.edges_directed(i, Incoming) {
            let dep = g.node_weight(e_ref.source()).unwrap().at;
            let edge = e_ref.weight();
            match edge.kind {
                DepEdgeKind::Control => {
                    ctrl_deps.insert(dep);
                }
                DepEdgeKind::Data => {
                    let arg_nums = arg_nums_for_dep(tcx, n.place, edge.at);
                    if let Some(&max) = arg_nums.iter().max() {
                        if input_deps.len() <= max {
                            input_deps.resize_with(max, HashSet::new);
                        }
                    }
                    for arg_num in arg_nums {
                        input_deps[arg_num].insert(dep);
                    }
                }
            }
        }
        DependencyResult::IsCall {
            node: n.at,
            deps: CallDeps {
                ctrl_deps,
                input_deps,
            },
        }
    }
}

impl CallOnlyFlow {
    pub fn from_dep_graph<'tcx>(tcx: TyCtxt<'tcx>, value: &DepGraph<'tcx>) -> Self {
        let mut return_dependencies = None;
        let location_dependencies = value.graph
            .node_indices()
            .filter_map(|i| {
                match dependencies_of_node(tcx, value, i) {
                    DependencyResult::IsReturn(return_deps) => {
                        assert!(return_dependencies.replace(return_deps).is_none());
                        None
                    }
                    DependencyResult::Skip => None,
                    DependencyResult::IsCall { node, deps } => Some((node, deps))
                }
            })
            .collect();

        CallOnlyFlow {
            location_dependencies,
            return_dependencies: return_dependencies.unwrap(),
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
