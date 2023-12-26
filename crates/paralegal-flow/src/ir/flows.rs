use crate::utils::CallStringExt;
use crate::{
    mir,
    pdg::*,
    utils::{AsFnAndArgs, TyCtxtExt},
    Either, HashMap, HashSet, TyCtxt,
};
use itertools::Itertools;
use petgraph::data::DataMap;
use petgraph::graph::NodeIndex;
use petgraph::visit::{
    depth_first_search, Data, DfsEvent, EdgeFiltered, GraphBase, IntoEdgeReferences,
    IntoEdgesDirected, IntoNodeReferences, Reversed,
};
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

fn as_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    location: GlobalLocation,
) -> Option<&'tcx mir::Terminator<'tcx>> {
    if let LocationOrStart::Location(loc) = location.location {
        tcx.body_for_def_id(location.function)
            .unwrap()
            .body
            .stmt_at(loc)
            .right()
    } else {
        None
    }
}

fn is_call(tcx: TyCtxt, location: GlobalLocation) -> bool {
    let Some(term) = as_terminator(tcx, location) else {
        return false;
    };
    matches!(term.kind, mir::TerminatorKind::Call { .. })
}

fn is_statement(tcx: TyCtxt, location: GlobalLocation) -> bool {
    as_terminator(tcx, location).is_none()
}

fn search_ancestors<'tcx, G, I>(
    tcx: TyCtxt<'tcx>,
    g: G,
    start: I,
    result: &mut impl Extend<CallString>,
) where
    G: petgraph::visit::IntoNeighbors
        + petgraph::visit::Visitable
        + GraphBase<NodeId = NodeIndex>
        + Data<NodeWeight = DepNode<'tcx>, EdgeWeight = DepEdge>
        + DataMap
        + IntoEdgeReferences
        + IntoEdgesDirected,
    I: IntoIterator<Item = G::NodeId>,
{
    use petgraph::visit::{Control, EdgeRef};
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
    let filtered = EdgeFiltered::from_fn(g, |e| {
        let w: &DepEdge = e.weight();
        matches!(w.kind, DepEdgeKind::Data)
    });
    depth_first_search(Reversed(&filtered), start, |event| match event {
        DfsEvent::Discover(node, _) => {
            let weight = g.node_weight(node).unwrap();
            if is_call(tcx, weight.at.leaf()) {
                result.extend(Some(weight.at));
                Control::Prune
            } else {
                Control::<()>::Continue
            }
        }
        _ => Control::Continue,
    });
}

fn place_contains<'tcx>(parent: mir::Place<'tcx>, child: mir::Place<'tcx>) -> bool {
    parent.local == child.local
        && parent
            .projection
            .iter()
            .eq(child.projection.iter().take(parent.projection.len()))
}

impl CallOnlyFlow {
    pub fn from_dep_graph<'tcx>(tcx: TyCtxt<'tcx>, value: &DepGraph<'tcx>) -> Self {
        use petgraph::visit::EdgeRef;
        let locations = value
            .graph
            .edge_references()
            .filter_map(|e| {
                let target_weight = value.graph.node_weight(e.target()).unwrap();
                is_call(tcx, target_weight.at.leaf())
                    .then_some((target_weight.at, (target_weight.place, e)))
            })
            .into_grouping_map()
            .fold(
                (HashMap::new(), vec![]),
                |(mut map, mut ctrl_deps), _, (place, e)| {
                    let target = if e.weight().kind == DepEdgeKind::Control {
                        &mut ctrl_deps
                    } else {
                        map.entry(place).or_insert_with(Vec::new)
                    };
                    target.push(e.source());
                    (map, ctrl_deps)
                },
            );
        let location_dependencies: HashMap<_, _> = locations
            .into_iter()
            .filter_map(|(location, (mut place_deps, direct_control_deps))| {
                let term = as_terminator(tcx, location.leaf())?;
                let (_, args, ret) = term.as_fn_and_args(tcx).unwrap();
                // First we find exact matches for each input place, popping them out of the map
                let mut input_deps: Vec<_> = args
                    .iter()
                    .map(|op| {
                        let mut deps = HashSet::new();
                        if let Some(dep_nodes) = op.and_then(|place| place_deps.remove(&place)) {
                            search_ancestors(tcx, &value.graph, dep_nodes, &mut deps);
                        }
                        deps
                    })
                    .collect();
                // For the rest we try to find matching subplaces and add them there too
                // XXX: I'm not sure that this composes properly with references.
                for (place, dep) in place_deps {
                    let mut matching_indices = args
                        .iter()
                        .zip(input_deps.iter_mut())
                        .filter_map(|(op, deps)| {
                            op.map_or(false, |op| place_contains(op, place))
                                .then_some(deps)
                        })
                        .peekable();
                    if matching_indices.peek().is_none() && !place_contains(ret, place) {
                        warn!(
                            "No matching argument found for place {place:?} in terminator {:?}",
                            term.kind
                        );
                    }
                    for deps in matching_indices {
                        search_ancestors(tcx, &value.graph, dep.iter().copied(), deps)
                    }
                }
                // Handle the same place being passed twice
                for (idx, op) in args.iter().enumerate() {
                    if let Some(op) = op {
                        if let Some(repeat_idx) = args[idx + 1..]
                            .iter()
                            .enumerate()
                            .find_map(|(i, elem)| (*elem == Some(*op)).then_some(i))
                        {
                            let (head, tail) = input_deps.split_at_mut(idx + 1);
                            tail[repeat_idx] = head.last().unwrap().clone();
                        }
                    }
                }
                let mut ctrl_deps = HashSet::new();
                search_ancestors(tcx, &value.graph, direct_control_deps, &mut ctrl_deps);
                Some((
                    location,
                    CallDeps {
                        input_deps,
                        ctrl_deps,
                    },
                ))
            })
            .collect();
        let mut return_dependencies = HashSet::new();
        search_ancestors(
            tcx,
            &value.graph,
            value
                .graph
                .node_references()
                .filter(|(_, n)| n.place == mir::RETURN_PLACE.into() && n.at.is_at_root())
                .map(|t| t.0),
            &mut return_dependencies,
        );

        for dep in return_dependencies
            .iter()
            .chain(location_dependencies.iter().flat_map(|(k, v)| {
                v.input_deps
                    .iter()
                    .flatten()
                    .chain(&v.ctrl_deps)
                    .chain(Some(k))
            }))
        {
            if let LocationOrStart::Location(loc) = dep.leaf().location {
                match tcx
                    .body_for_def_id(dep.leaf().function)
                    .unwrap()
                    .body
                    .stmt_at(loc)
                {
                    Either::Left(stmt) => panic!("Found statement at location {dep}: {stmt:?}"),
                    Either::Right(term)
                        if !matches!(term.kind, mir::TerminatorKind::Call { .. }) =>
                    {
                        panic!(
                            "Found non-call terminator at location {dep}: {:?}",
                            term.kind
                        )
                    }
                    _ => (),
                }
            }
        }

        CallOnlyFlow {
            location_dependencies,
            return_dependencies,
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
