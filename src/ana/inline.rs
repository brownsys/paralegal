//! The [`Inliner`]. The 30s summary of what this does is 
//! 1. It starts from single-procedure analyses ([`regal::Body`])
//! 2. Turns them into graphs ([`ProcedureGraph`])
//! 3. Turns locations into global locations in both the graph and in the
//!    equations ([`InlinedGraph`])
//! 4. Inlines callees that are (un)marked. In the graphs the nodes are are
//!    replaced by the callee graph, reconnecting incoming and outgoing edges at
//!    the boundary. Callee locations are relativized ([`GliAt::relativize`]).
//!    Callee equations also have the bases rewritten
//!    ([`Inliner::relativize_eqs`]) before being added to the caller equations.
//! 5. Use the equations from place analysis prune edges
//!    ([`InlinedGraph::prune_impossible_edges`]) using the accumulated set of
//!    equations

use flowistry::{cached::Cache, mir::borrowck_facts};
use petgraph::{
    prelude as pg,
    visit::{EdgeRef, IntoEdgeReferences, IntoNodeReferences},
};

use crate::{
    ana::algebra::{self, Term},
    hir::BodyId,
    ir::{
        flows::CallOnlyFlow,
        global_location::IsGlobalLocation,
        regal::{self, SimpleLocation},
        GliAt, GlobalLocation, GLI,
    },
    mir,
    mir::Location,
    outfile_pls,
    rust::hir::def_id::{DefId, LocalDefId},
    rust::rustc_index::vec::IndexVec,
    ty,
    utils::{body_name_pls, AsFnAndArgs, DisplayViaDebug},
    Either, HashMap, HashSet, TyCtxt,
};

/// This essentially describes a closure that determines for a given
/// [`LocalDefId`] if it should be inlined. Originally this was in fact done by
/// passing a closure, but it couldn't properly satisfy the type checker,
/// because the selector has to be stored in `fluid_let` variable, which is a
/// dynamically scoped variable. This means that the type needs to be valid for
/// a static lifetime, which I believe closures are not.
///
/// In particular the way that this works is that values of this interface are
/// then wrapped with [`RecurseSelector`], which is a flowistry interface that
/// satisfies [`flowistry::extensions::RecurseSelector`]. The wrapper then
/// simply dispatches to the [`InlineSelector`].
///
/// The reason for the two tiers of selectors is that
///
/// - Flowistry is a separate crate and so I wanted a way to control it that
///   decouples from the specifics of dfpp
/// - We use the selectors to skip functions with annotations, but I wanted to
///   keep the construction of inlined flow graphs agnostic to any notion of
///   annotations. Those are handled by the [`CollectingVisitor`]
///
/// The only implementation currently in use for this is
/// [`SkipAnnotatedFunctionSelector`].
pub trait InlineSelector: 'static {
    fn should_inline(&self, tcx: TyCtxt, did: LocalDefId) -> bool;
}

impl<T: InlineSelector> InlineSelector for std::rc::Rc<T> {
    fn should_inline(&self, tcx: TyCtxt, did: LocalDefId) -> bool {
        self.as_ref().should_inline(tcx, did)
    }
}

type ArgNum = regal::ArgumentIndex;

type Node<C> = regal::SimpleLocation<C>;

impl<C> Node<C> {
    fn map_call<C0, F: FnOnce(&C) -> C0>(&self, f: F) -> Node<C0> {
        match self {
            Node::Return => Node::Return,
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

/// Common, parameterized equation type used by the [`GraphResolver`]s
pub type Equation<L> =
    algebra::Equality<Node<regal::RelativePlace<L>>, DisplayViaDebug<mir::Field>>;
pub type Equations<L> = Vec<Equation<L>>;
/// Common, parameterized graph type used in this module
pub type GraphImpl<L> = pg::StableDiGraph<Node<(L, DefId)>, Edge>;

/// A graph and the associated set of extracted or accumulated equations
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

/// A graph describing the relationships of call sites, arguments and return
/// values for a single analyzed function.
type ProcedureGraph = GraphWithResolver<DisplayViaDebug<Location>>;
/// A graph describing the relationship of call sites, arguments and return
/// values for an analyzed functions with certain called functions inlined/expanded,
type InlinedGraph<'g> = GraphWithResolver<GlobalLocation<'g>>;

impl<'g> InlinedGraph<'g> {
    /// For each edge in this graph query the set of equations to determine if
    /// it is memory-plausible e.g. if there exists an argument `a` to the
    /// target and a return `r` from the source such that either `a` can be
    /// reached from `r` or `r` can be reached from `a`. 
    /// 
    /// The simples example is where `r == a` a more complex example could be
    /// that `r = *a.foo`.
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
            let to_target = to_weight.map_location(|&(location, _did)| regal::RelativePlace {
                location,
                place: regal::TargetPlace::Argument(*target_index),
            });
            let from_weight = graph.node_weight(from).unwrap();
            let targets = match from_weight {
                Node::Argument(a) => {
                    Either::Right(std::iter::once(regal::SimpleLocation::Argument(*a)))
                }
                Node::Return => unreachable!(),
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
                for r in result {
                    reached |= Term::from_raw(0, r).simplify();
                }
            }
            if !reachable {
                debug!("Found unreproducible edge {from_weight} -> {to_weight}");
            }
            reached
        })
    }
}

impl From<regal::Body<DisplayViaDebug<Location>>> for ProcedureGraph {
    fn from(body: regal::Body<DisplayViaDebug<Location>>) -> Self {
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
        let arg_map = IndexVec::from_raw(
            body.return_arg_deps
                .iter()
                .enumerate()
                .map(|(i, _)| g.add_node(SimpleLocation::Argument(ArgNum::from_usize(i))))
                .collect(),
        );

        let return_node = g.add_node(Node::Return);

        let mut add_dep_edges =
            |target_id, idx, deps: &HashSet<regal::Target<DisplayViaDebug<Location>>>| {
                for d in deps {
                    use regal::Target;
                    let from = match d {
                        Target::Call(c) => node_map[&c],
                        Target::Argument(a) => arg_map[*a],
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
        for (idx, deps) in body.return_arg_deps.iter().enumerate() {
            add_dep_edges(arg_map[ArgNum::from_usize(idx)], 0, deps);
        }

        gwr
    }
}

/// Essentially just a bunch of caches of analyses.
pub struct Inliner<'tcx, 'g, 's> {
    /// Memoized graphs created from single-procedure analyses
    base_memo: Cache<BodyId, ProcedureGraph>,
    /// Memoized graphs that have all their callees inlined
    inline_memo: Cache<BodyId, InlinedGraph<'g>>,
    /// Selects which callees to inline.
    recurse_selector: &'s dyn InlineSelector,
    tcx: TyCtxt<'tcx>,
    gli: GLI<'g>,
}

/// Globalize all locations mentioned in these equations.
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

/// Does a naïve transformation from a [`ProcedureGraph`] into a
/// [`InlinedGraph`]. It just globalizes the locations, it does not actually
/// perform inlining (despite what the name of the returned type might suggest).
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

    /// Compute a procedure graph for this `body_id` (memoized). Actual
    /// computation performed by [`regal::compute_from_body_id`] and
    /// [`ProcedureGraph::from`]
    fn get_procedure_graph(&self, body_id: BodyId) -> &ProcedureGraph {
        self.base_memo.get(body_id, |bid| {
            regal::compute_from_body_id(bid, self.tcx, self.gli).into()
        })
    }

    /// Compute an inlined graph for this `body_id` (memoized)
    pub fn get_inlined_graph(&self, body_id: BodyId) -> &InlinedGraph<'g> {
        self.inline_memo.get(body_id, |bid| self.inline_graph(bid))
    }

    /// Convenience wrapper around [`Self::get_inlined_graph`]
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
                    Argument(aidx) => regal::RelativePlace {
                        location: gli.as_global_location(),
                        place: regal::TargetPlace::Argument(*aidx),
                    },
                    Return => regal::RelativePlace {
                        location: gli.as_global_location(),
                        place: regal::TargetPlace::Return,
                    },
                })
            })
        })
    }

    fn writeable_arguments<'tc>(
        fn_sig: &ty::FnSig<'tc>,
    ) -> impl Iterator<Item = regal::ArgumentIndex> + 'tc {
        fn_sig.inputs().iter().enumerate().filter_map(|(i, t)| {
            t.is_mutable_ptr()
                .then(|| regal::ArgumentIndex::from_usize(i))
        })
    }

    /// In spite of the name of this function it not only inlines the graph but
    /// also first creates it (with [`Self::get_procedure_graph`]) and globalize
    /// it ([`to_global_graph`]).
    fn inline_graph(&self, body_id: BodyId) -> InlinedGraph<'g> {
        let proc_g = self.get_procedure_graph(body_id);
        let local_def_id = self.tcx.hir().body_owner_def_id(body_id);
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
                        Some((id, local_id, *location, false))
                    }
                    _ if Some(*function) == self.tcx.lang_items().from_generator_fn() => {
                        let body_with_facts =
                            borrowck_facts::get_body_with_borrowck_facts(self.tcx, local_def_id);
                        let body = body_with_facts.simplified_body();
                        let mut args = body
                            .stmt_at(location.innermost_location_and_body().0)
                            .right()
                            .expect("Expected terminator")
                            .as_fn_and_args()
                            .unwrap()
                            .1;
                        let closure = args
                            .pop()
                            .expect("Expected one closure argument")
                            .expect("Expected non-const closure argument");
                        debug_assert!(args.is_empty(), "Expected only one argument");
                        debug_assert!(closure.projection.is_empty());
                        let closure_fn = if let ty::TyKind::Generator(gid, _, _) =
                            body.local_decls[closure.local].ty.kind()
                        {
                            *gid
                        } else {
                            unreachable!("Expected Generator")
                        };
                        Some((id, closure_fn.as_local().unwrap(), *location, true))
                    }
                    _ => {
                        debug!("Abstracting {function:?}");
                        let fn_sig = self.tcx.fn_sig(function).skip_binder();
                        let writeables = std::iter::once(regal::TargetPlace::Return)
                            .chain(
                                Self::writeable_arguments(&fn_sig)
                                    .map(regal::TargetPlace::Argument),
                            )
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
                                    algebra::Equality::new(
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
        for (idx, def_id, root_location, is_async_closure) in targets {
            let num_args = if is_async_closure {
                1 as usize
            } else {
                self.tcx.fn_sig(def_id).skip_binder().inputs().len()
            };
            let mut argument_map: HashMap<_, _> = (0..num_args)
                .map(|a| (ArgNum::from_usize(a), vec![]))
                .collect();

            for e in g.edges_directed(idx, pg::Incoming) {
                let arg_num = e.weight().target_index;
                argument_map.get_mut(&arg_num).unwrap().push(e.source());
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
                        debug!("  adding edge to {}", g.node_weight(*c).unwrap());
                        g.add_edge(*c, target, weight.clone());
                    }
                    Node::Return => unreachable!(),
                    Node::Argument(a) => {
                        debug!("  found argument");
                        for nidx in argument_map.get(a).into_iter().flat_map(|s| s.into_iter()) {
                            debug!("  adding edge to {}", g.node_weight(*nidx).unwrap());
                            g.add_edge(*nidx, target, weight.clone());
                        }
                    }
                };

            for (callee_id, typ) in node_map.iter() {
                debug!(
                    "Handling node {}",
                    to_inline.node_weight(*callee_id).unwrap()
                );
                match typ {
                    Node::Call(new_id) => {
                        for edge in to_inline.edges_directed(*callee_id, pg::Incoming) {
                            connect_to(g, edge.source(), *new_id, edge.weight())
                        }
                    }
                    Node::Return | Node::Argument(_) => {
                        for edge in to_inline.edges_directed(*callee_id, pg::Incoming) {
                            debug!("  for incoming edge {:?}", edge.id());
                            for (target, out) in g
                                .edges_directed(idx, pg::Outgoing)
                                .map(|e| (e.target(), e.weight().clone()))
                                .collect::<Vec<_>>()
                            {
                                connect_to(g, edge.source(), target, &out);
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

/// Turn the output of the inliner into the format the rest of the dfpp pipeline
/// understands.
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
                Node::Return => unreachable!(),
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
            Node::Return => {
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
