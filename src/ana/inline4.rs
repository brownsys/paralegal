use std::fmt::Write;

use flowistry::cached::Cache;
use petgraph::{
    prelude as pg,
    visit::{EdgeRef, IntoEdgeReferences, IntoEdgesDirected, IntoNodeReferences, NodeRef},
};

use crate::{
    ana::algebra::{self, Term},
    hir::BodyId,
    ir::{
        flows::CallOnlyFlow,
        global_location::IsGlobalLocation,
        regal::{self, TargetPlace},
        GliAt, GlobalLocation, GLI,
    },
    mir,
    mir::Location,
    outfile_pls,
    rust::hir::def_id::{DefId, LocalDefId},
    utils::{body_name_pls, DisplayViaDebug},
    Either, HashMap, HashSet, TyCtxt,
};

use super::{algebra::Equality, inline::InlineSelector};

type ArgNum = regal::ArgumentIndex;

type Node<C> = regal::SimpleLocation<C>;

impl<C> Node<C> {
    fn map_call<C0, F: FnOnce(&C) -> C0>(&self, f: F) -> Node<C0> {
        match self {
            Node::Return(r) => Node::Return(*r),
            Node::Argument(a) => Node::Argument(*a),
            Node::Call(c) => Node::Call(f(c)),
        }
    }
}

#[derive(Clone)]
pub struct Edge {
    target_index: ArgNum,
}

impl std::fmt::Display for Edge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.target_index)
    }
}

pub type Equation<L> =
    algebra::Equality<Node<regal::RelativePlace<L>>, DisplayViaDebug<mir::Field>>;
pub type Equations<L> = Vec<Equation<L>>;
pub type GraphImpl<L> = pg::StableDiGraph<Node<(L, DefId)>, Edge>;

pub struct GraphWithResolver<L> {
    graph: GraphImpl<L>,
    equations: Equations<L>,
}

impl<L> Default for GraphWithResolver<L> {
    fn default() -> Self {
        Self {
            graph: pg::StableDiGraph::new(),
            equations: vec![],
        }
    }
}

type ProcedureGraph = GraphWithResolver<DisplayViaDebug<Location>>;
type InlinedGraph<'g> = GraphWithResolver<GlobalLocation<'g>>;

impl<C> Node<C> {
    fn into_target_with<C0, F: FnOnce(&C) -> C0>(&self, f: F) -> Option<regal::Target<C0>> {
        match self {
            Node::Return(_) => None,
            Node::Argument(a) => Some(regal::Target::Argument(*a)),
            Node::Call(c) => Some(regal::Target::Call(f(c))),
        }
    }
}

impl<'g> InlinedGraph<'g> {
    fn prune_impossible_edges<'tcx>(&mut self, tcx: TyCtxt<'tcx>) {
        debug!(
            "Equations for pruning are:\n{}",
            crate::utils::Print(|f: &mut std::fmt::Formatter<'_>| {
                for eq in self.equations.iter() {
                    writeln!(f, "  {eq}")?;
                }
                Ok(())
            })
        );
        self.graph.retain_edges(|graph, idx| {
            let (from, to) = graph.edge_endpoints(idx).unwrap();
            let Edge { target_index } = graph.edge_weight(idx).unwrap();
            let to_weight = graph.node_weight(to).unwrap();
            let to_target = to_weight.map_location(|&(location, did)| regal::RelativePlace {
                location,
                place: regal::TargetPlace::Argument(*target_index),
            });
            let from_weight = graph.node_weight(from).unwrap();
            let targets = match from_weight {
                Node::Argument(a) => {
                    Either::Right(std::iter::once(regal::SimpleLocation::Argument(*a)))
                }
                Node::Return(_) => unreachable!(),
                Node::Call((location, did)) => Either::Left({
                    let args = tcx.fn_sig(did).skip_binder().inputs().len();
                    (0..args)
                        .into_iter()
                        .map(|a| {
                            regal::SimpleLocation::Call(regal::RelativePlace {
                                location: *location,
                                place: regal::TargetPlace::Argument(
                                    regal::ArgumentIndex::from_usize(a),
                                ),
                            })
                        })
                        .chain(std::iter::once(regal::SimpleLocation::Call(
                            regal::RelativePlace {
                                location: *location,
                                place: regal::TargetPlace::Return,
                            },
                        )))
                }),
            };
            let mut reachable = false;
            let mut reached = false;
            for from_target in targets {
                let result = algebra::solve(&self.equations, &to_target, &from_target);
                reachable |= !result.is_empty();
                for mut r in result {
                    reached |= Term::from_raw(0, r).simplify();
                }
            }
            if !reachable {
                warn!("Found unreproducible edge {from_weight} -> {to_weight}");
            }
            reached
        })
    }
}

impl From<regal::Body2<DisplayViaDebug<Location>>> for ProcedureGraph {
    fn from(body: regal::Body2<DisplayViaDebug<Location>>) -> Self {
        let mut gwr = ProcedureGraph::default();
        debug!(
            "Equations for body are:\n{}",
            crate::utils::Print(|f: &mut std::fmt::Formatter<'_>| {
                for eq in body.equations.iter() {
                    writeln!(f, "  {eq}")?;
                }
                Ok(())
            })
        );
        gwr.equations = body.equations;
        let g = &mut gwr.graph;
        let node_map = body
            .calls
            .iter()
            .map(|(loc, call)| (*loc, g.add_node(Node::Call((*loc, call.function)))))
            .collect::<HashMap<_, _>>();
        let mut arg_map = HashMap::new();

        let return_node = g.add_node(Node::Return(None));
        let return_arg_nodes = body
            .return_arg_deps
            .iter()
            .enumerate()
            .map(|(i, _)| g.add_node(Node::Return(Some(ArgNum::from_usize(i)))))
            .collect::<Vec<_>>();

        let mut add_dep_edges =
            |target_id, idx, deps: &HashSet<regal::Target<DisplayViaDebug<Location>>>| {
                for d in deps {
                    use regal::Target;
                    let from = match d {
                        Target::Call(c) => node_map[&c],
                        Target::Argument(a) => *arg_map
                            .entry(*a)
                            .or_insert_with(|| g.add_node(Node::Argument(*a))),
                    };
                    g.add_edge(
                        from,
                        target_id,
                        Edge {
                            target_index: ArgNum::from_usize(idx),
                        },
                    );
                }
            };

        for (n, call) in body.calls.iter() {
            let new_id = node_map[n];
            for (idx, deps) in call.arguments.iter().enumerate() {
                add_dep_edges(new_id, idx, deps)
            }
        }
        add_dep_edges(return_node, 0, &body.return_deps);
        for (deps, node) in body.return_arg_deps.iter().zip(return_arg_nodes.iter()) {
            add_dep_edges(*node, 0, deps);
        }

        debug!(
            "All nodes are:\n{}",
            crate::utils::Print(|f: &mut std::fmt::Formatter<'_>| {
                for n in g.node_references() {
                    writeln!(f, "  {:?}: {}", n.0, n.1)?;
                }
                Ok(())
            })
        );

        gwr
    }
}

pub struct Inliner<'tcx, 'g, 's> {
    base_memo: Cache<BodyId, ProcedureGraph>,
    inline_memo: Cache<BodyId, InlinedGraph<'g>>,
    recurse_selector: &'s dyn InlineSelector,
    tcx: TyCtxt<'tcx>,
    gli: GLI<'g>,
}

fn to_global_equations<'g>(
    eqs: &Equations<DisplayViaDebug<Location>>,
    body_id: BodyId,
    gli: GLI<'g>,
) -> Equations<GlobalLocation<'g>> {
    eqs.iter()
        .map(|eq| {
            eq.map_bases(|target| {
                target.map_location(|place| regal::RelativePlace {
                    place: place.place,
                    location: gli.globalize_location(*place.location, body_id),
                })
            })
        })
        .collect()
}

fn to_global_graph<'g>(
    ProcedureGraph {
        graph: proc_g,
        equations: local_eq,
    }: &ProcedureGraph,
    gli: GLI<'g>,
    body_id: BodyId,
) -> InlinedGraph<'g> {
    let mut gwr = InlinedGraph::default();
    gwr.equations = to_global_equations(local_eq, body_id, gli);
    let g = &mut gwr.graph;
    let node_map = proc_g
        .node_references()
        .map(|(n, w)| {
            (
                n,
                g.add_node(w.map_call(|(loc, id)| (gli.globalize_location(**loc, body_id), *id))),
            )
        })
        .collect::<HashMap<_, _>>();
    for e in proc_g.edge_references() {
        g.add_edge(
            node_map[&e.source()],
            node_map[&e.target()],
            e.weight().clone(),
        );
    }
    debug!(
        "All initial global nodes are:\n{}",
        crate::utils::Print(|f: &mut std::fmt::Formatter<'_>| {
            for n in g.node_references() {
                writeln!(f, "  {:?}: {}", n.0, n.1)?;
            }
            Ok(())
        })
    );
    gwr
}

impl<'tcx, 'g, 's> Inliner<'tcx, 'g, 's> {
    pub fn new(tcx: TyCtxt<'tcx>, gli: GLI<'g>, recurse_selector: &'s dyn InlineSelector) -> Self {
        Self {
            tcx,
            gli,
            recurse_selector,
            base_memo: Default::default(),
            inline_memo: Default::default(),
        }
    }

    fn get_procedure_graph(&self, body_id: BodyId) -> &ProcedureGraph {
        self.base_memo.get(body_id, |bid| {
            regal::compute2_from_body_id(bid, self.tcx, self.gli).into()
        })
    }

    pub fn get_inlined_graph(&self, body_id: BodyId) -> &InlinedGraph<'g> {
        self.inline_memo.get(body_id, |bid| self.inline_graph(bid))
    }

    fn get_inlined_graph_by_def_id(&self, def_id: LocalDefId) -> &InlinedGraph<'g> {
        let hir = self.tcx.hir();
        self.get_inlined_graph(hir.body_owned_by(hir.local_def_id_to_hir_id(def_id)))
    }

    fn relativize_eqs<'a>(
        equations: &'a Equations<GlobalLocation<'g>>,
        gli: &'a GliAt<'g>,
    ) -> impl Iterator<Item = Equation<GlobalLocation<'g>>> + 'a {
        equations.iter().map(move |eq| {
            eq.map_bases(|base| {
                use regal::SimpleLocation::*;
                Call(match base {
                    Call(place) => regal::RelativePlace {
                        place: place.place,
                        location: gli.relativize(place.location),
                    },
                    Argument(aidx) | Return(Some(aidx)) => regal::RelativePlace {
                        location: gli.as_global_location(),
                        place: regal::TargetPlace::Argument(*aidx),
                    },
                    Return(None) => regal::RelativePlace {
                        location: gli.as_global_location(),
                        place: regal::TargetPlace::Return,
                    },
                })
            })
        })
    }

    fn inline_graph(&self, body_id: BodyId) -> InlinedGraph<'g> {
        let proc_g = self.get_procedure_graph(body_id);
        let mut gwr = to_global_graph(proc_g, self.gli, body_id);

        dump_dot_graph(
            outfile_pls(format!(
                "{}.pre-inline.gv",
                body_name_pls(self.tcx, body_id)
            ))
            .unwrap(),
            &gwr,
        )
        .unwrap();
        let g = &mut gwr.graph;
        let eqs = &mut gwr.equations;
        let targets = g
            .node_references()
            .filter_map(|(id, n)| match n {
                Node::Call((location, function)) => match function.as_local() {
                    Some(local_id) if self.recurse_selector.should_inline(self.tcx, local_id) => {
                        debug!("Inlining {function:?}");
                        Some((id, function.as_local()?, *location))
                    }
                    _ => {
                        debug!("Abstracting {function:?}");
                        let fn_sig = self.tcx.fn_sig(function).skip_binder();
                        let writeables = std::iter::once(regal::TargetPlace::Return)
                            .chain(fn_sig.inputs().iter().enumerate().filter_map(|(i, t)| {
                                t.is_mutable_ptr().then(|| {
                                    regal::TargetPlace::Argument(regal::ArgumentIndex::from_usize(
                                        i,
                                    ))
                                })
                            }))
                            .collect::<Vec<_>>();
                        let mk_term = |tp| {
                            algebra::Term::new_base(regal::SimpleLocation::Call(
                                regal::RelativePlace {
                                    place: tp,
                                    location: *location,
                                },
                            ))
                        };
                        eqs.extend(writeables.iter().flat_map(|write| {
                            (0..fn_sig.inputs().len() as usize)
                                .map(|t| {
                                    regal::TargetPlace::Argument(regal::ArgumentIndex::from_usize(
                                        t,
                                    ))
                                })
                                .filter(move |read| read != write)
                                .map(|read| {
                                    Equality::new(
                                        mk_term(write.clone()).add_unknown(),
                                        mk_term(read),
                                    )
                                })
                        }));
                        None
                    }
                },
                _ => {
                    debug!("Is other node {n}");
                    None
                }
            })
            .collect::<Vec<_>>();
        for (idx, def_id, root_location) in targets {
            let mut argument_map = HashMap::new();

            for e in g.edges_directed(idx, pg::Incoming) {
                let arg_num = e.weight().target_index;
                argument_map
                    .entry(arg_num)
                    .or_insert_with(|| vec![])
                    .push(e.source());
            }

            let grw_to_inline = self.get_inlined_graph_by_def_id(def_id);
            assert!(root_location.is_at_root());
            let gli_here = self.gli.at(root_location.location(), body_id);
            gwr.equations
                .extend(Self::relativize_eqs(&grw_to_inline.equations, &gli_here));
            let to_inline = &grw_to_inline.graph;
            let node_map = to_inline
                .node_references()
                .map(|(callee_id, node)| {
                    (
                        callee_id,
                        node.map_call(|(location, function)| {
                            g.add_node(Node::Call((gli_here.relativize(*location), *function)))
                        }),
                    )
                })
                .collect::<HashMap<_, _>>();

            let connect_to =
                |g: &mut GraphImpl<_>, source, target, weight: &Edge| match &node_map[&source] {
                    Node::Call(c) => {
                        g.add_edge(*c, target, weight.clone());
                    }
                    Node::Return(_) => unreachable!(),
                    Node::Argument(a) => {
                        for nidx in argument_map.get(a).into_iter().flat_map(|s| s.into_iter()) {
                            g.add_edge(*nidx, target, weight.clone());
                        }
                    }
                };

            for (callee_id, typ) in node_map.iter() {
                match typ {
                    Node::Call(new_id) => {
                        for parent in to_inline.edges_directed(*callee_id, pg::Incoming) {
                            connect_to(g, parent.source(), *new_id, parent.weight())
                        }
                    }
                    Node::Argument(_) => (),
                    Node::Return(a) => {
                        for parent in to_inline.edges_directed(*callee_id, pg::Incoming) {
                            for (target, out) in g
                                .edges_directed(idx, pg::Outgoing)
                                .map(|e| (e.target(), e.weight().clone()))
                                .collect::<Vec<_>>()
                            {
                                connect_to(g, parent.source(), target, &out);
                            }
                        }
                    }
                }
            }
            g.remove_node(idx);
        }
        dump_dot_graph(
            outfile_pls(format!("{}.inlined.gv", body_name_pls(self.tcx, body_id))).unwrap(),
            &gwr,
        )
        .unwrap();
        gwr.prune_impossible_edges(self.tcx);
        dump_dot_graph(
            outfile_pls(format!(
                "{}.inlined-pruned.gv",
                body_name_pls(self.tcx, body_id)
            ))
            .unwrap(),
            &gwr,
        )
        .unwrap();
        gwr
    }
}

fn dump_dot_graph<L: std::fmt::Display, W: std::io::Write>(
    mut w: W,
    g: &GraphWithResolver<L>,
) -> std::io::Result<()> {
    use petgraph::dot::*;
    write!(
        w,
        "{}",
        Dot::with_attr_getters(&g.graph, &[], &|_, _| "".to_string(), &|_, _| "shape=box"
            .to_string(),)
    )
}

pub fn to_call_only_flow<'g, A: FnMut(ArgNum) -> GlobalLocation<'g>>(
    InlinedGraph { graph: g, .. }: &InlinedGraph<'g>,
    mut mk_arg: A,
) -> crate::ir::CallOnlyFlow<GlobalLocation<'g>> {
    let mut location_dependencies = HashMap::new();
    let mut return_dependencies = HashSet::new();

    let mut get_dependencies = |n| {
        let mut input_deps = vec![];
        for e in g.edges_directed(n, pg::Incoming) {
            let aidx = e.weight().target_index.as_usize();
            if aidx >= input_deps.len() {
                input_deps.resize_with(aidx + 1, HashSet::new);
            }
            input_deps[aidx].insert(match g.node_weight(e.source()).unwrap() {
                Node::Call(c) => c.0,
                Node::Return(_) => unreachable!(),
                Node::Argument(a) => mk_arg(*a),
            });
        }
        crate::ir::CallDeps {
            input_deps,
            ctrl_deps: HashSet::new(),
        }
    };

    for (idx, n) in g.node_references() {
        match n {
            Node::Argument(_) => (),
            Node::Return(_) => {
                for d in get_dependencies(idx)
                    .input_deps
                    .iter()
                    .flat_map(HashSet::iter)
                {
                    return_dependencies.insert(*d);
                }
            }
            Node::Call((loc, _)) => assert!(location_dependencies
                .insert(*loc, get_dependencies(idx))
                .is_none()),
        }
    }

    CallOnlyFlow {
        location_dependencies,
        return_dependencies,
    }
}
