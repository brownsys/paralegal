use petgraph::{prelude as pg, visit::{IntoNodeReferences, IntoEdgesDirected, EdgeRef}};
use flowistry::cached::Cache;

use crate::{
    hir::BodyId,
    mir::{Location},
    ir::{GlobalLocation, GLI, regal, global_location::IsGlobalLocation, flows::CallOnlyFlow},
    rust::hir::{def_id::{DefId, LocalDefId}}, utils::DisplayViaDebug,
    TyCtxt,HashMap, HashSet
};

use super::inline::InlineSelector;

type ArgNum = regal::ArgumentIndex;

pub enum Node<C> {
    Return,
    Argument(ArgNum),
    Call(C)
}

#[derive(Clone)]
pub struct Edge {
    target_index: ArgNum,
    term: regal::TargetTerm,
}

type ProcedureGraph = pg::StableDiGraph<Node<(Location, DefId)>, Edge>;
type InlinedGraph<'g> = pg::StableDiGraph<Node<(GlobalLocation<'g>, DefId)>, Edge>;

impl From<&'_ regal::Body<DisplayViaDebug<Location>>> for ProcedureGraph {
    fn from(body: &regal::Body<DisplayViaDebug<Location>>) -> Self {
        todo!()
    }
}

pub struct Inliner<'tcx, 'g, 's> {
    base_memo: Cache<BodyId, ProcedureGraph>,
    inline_memo: Cache<BodyId, InlinedGraph<'g>>,
    recurse_selector: &'s dyn InlineSelector,
    tcx: TyCtxt<'tcx>,
    gli: GLI<'g>,
}

fn to_global_graph<'g>(proc_g: &ProcedureGraph, gli: GLI<'g>) -> InlinedGraph<'g> {
    todo!()
}

impl <'tcx, 'g, 's> Inliner<'tcx, 'g, 's> {
    pub fn new(tcx: TyCtxt<'tcx>, gli: GLI<'g>, recurse_selector: &'s dyn InlineSelector) -> Self {
        Self {
            tcx, gli, recurse_selector, base_memo: Default::default(), inline_memo: Default::default()
        }
    }

    fn get_procedure_graph(&self, body_id: BodyId) -> &ProcedureGraph {
        self.base_memo.get(
            body_id,
            |bid| {
                (&regal::compute_from_body_id(bid, self.tcx, self.gli)).into()
            }
        )
    }

    pub fn get_inlined_graph(&self, body_id: BodyId) -> &InlinedGraph<'g> {
        self.inline_memo.get(body_id, |bid| self.inline_graph(bid))
    }

    fn get_inlined_graph_by_def_id(&self, def_id: LocalDefId) -> &InlinedGraph<'g> {
        let hir = self.tcx.hir();
        self.get_inlined_graph(hir.body_owned_by(hir.local_def_id_to_hir_id(def_id)))
    }

    fn inline_graph(&self, body_id: BodyId) -> InlinedGraph<'g> {
        let proc_g = self.get_procedure_graph(body_id);
        let mut g = to_global_graph(proc_g, self.gli);
        let targets = g.node_references().filter_map(|(id, n)| match n {
            Node::Call (( location , function )) if self.recurse_selector.should_inline(self.tcx, function.as_local()?) => Some((id, function.as_local()?, *location)),
            _ => None
        }).collect::<Vec<_>>();
        for (idx, def_id, root_location) in targets {
            let mut argument_map = HashMap::new();

            for e in g.edges_directed(idx, pg::Incoming) {
                argument_map.entry(e.weight().target_index).or_insert_with(|| vec![]).push((e.source(), e.weight().term.clone()));
            }

            let to_inline = self.get_inlined_graph_by_def_id(def_id);
            let node_map = to_inline.node_references().map(|(callee_id, node)| (callee_id, 
                match node {
                    Node::Call (( location, function )) => 
                        Node::Call(g.add_node(Node::Call((
                            self.gli.global_location_from_relative(*location, root_location.location(), body_id),
                            *function,
                        )))),
                Node::Argument(a) => Node::Argument(*a),
                Node::Return => Node::Return,
            })
            ).collect::<HashMap<_, _>>();

            let connect_to = |g: &mut InlinedGraph<'g>, source, target, weight: &Edge| {
                 match &node_map[&source] {
                    Node::Call(c) => { g.add_edge(*c, target, weight.clone()); },
                    Node::Return => unreachable!(),
                    Node::Argument(a) => {
                        for (nidx, term) in &argument_map[a]  {
                            let Edge { target_index: pidx, term: pterm} = weight;
                            let mut new_term = pterm.clone();
                            new_term.sub(term.clone());
                            if new_term.simplify() {
                                g.add_edge(*nidx, target, Edge { target_index: *pidx, term: new_term});
                            }
                        }
                    }
                }
            };

            for (callee_id, typ) in node_map.iter() {
                match typ {
                    Node::Call(new_id) => {
                        for parent in to_inline.edges_directed(*callee_id, pg::Incoming) {
                            connect_to(&mut g, parent.source(), *new_id, parent.weight())
                        }
                    }
                    Node::Argument(_) => (),
                    Node::Return => {
                        for parent in to_inline.edges_directed(*callee_id, pg::Incoming) {
                            for (target, out) in g.edges_directed(idx, pg::Outgoing).map(|e| (e.target(), e.weight().clone())).collect::<Vec<_>>() {
                                let Edge { term: pterm, .. } = parent.weight();
                                let Edge {term: cterm, target_index: cidx } = out;
                                let mut new_term = cterm.clone();
                                new_term.sub(pterm.clone());
                                if new_term.simplify() {
                                    connect_to(&mut g, parent.source(), target, &Edge { target_index: cidx, term: new_term});
                                }
                            }
                        }
                    }
                }
            }
        }
        g
    }
}

pub fn to_call_only_flow<'g, A: FnMut(ArgNum) -> GlobalLocation<'g>>(g: &InlinedGraph<'g>, mut mk_arg: A) -> crate::ir::CallOnlyFlow<GlobalLocation<'g>> {
    let mut location_dependencies = HashMap::new();
    let mut return_dependencies = HashSet::new();

    let mut get_dependencies = |n| {
        let mut input_deps = vec![];
        for e in g.edges_directed(n, pg::Incoming) {
            let aidx = e.weight().target_index.as_usize();
            if aidx >= input_deps.len() {
                input_deps.resize_with(aidx, HashSet::new);
            }
            input_deps[aidx].insert(match g.node_weight(e.source()).unwrap() {
                Node::Call(c) => c.0,
                Node::Return => unreachable!(),
                Node::Argument(a) => mk_arg(*a),
            });
        }
        crate::ir::CallDeps {
            input_deps, ctrl_deps: HashSet::new()
        }
    };

    for (idx, n) in g.node_references() {
        match n {
            Node::Argument(_) => (),
            Node::Return => return_dependencies = get_dependencies(idx).input_deps.into_iter().flat_map(HashSet::into_iter).collect(),
            Node::Call((loc, _)) => 
                assert!(location_dependencies.insert(*loc, get_dependencies(idx)).is_none())
        }
    }

    CallOnlyFlow {
        location_dependencies, return_dependencies
    }
}
