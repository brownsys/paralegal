use crate::{
    ann::MarkerAnnotation,
    desc::*,
    discover::FnToAnalyze,
    rust::{hir::def, *},
    stats::TimedStat,
    utils::*,
    DefId, HashMap, HashSet, MarkerCtx,
};
use flowistry_pdg::SourceUse;
use paralegal_spdg::Node;

use std::{borrow::Cow, rc::Rc, time::Instant};

use super::{default_index, inline_judge, path_for_item, src_loc_for_span, SPDGGenerator};
use anyhow::{anyhow, Result};
use either::Either;
use flowistry_pdg_construction::{
    graph::{DepEdge, DepEdgeKind, DepGraph, DepNode},
    is_async_trait_fn, match_async_trait_assign, try_resolve_function, CallChanges, PdgParams,
    SkipCall::Skip,
};
use petgraph::{
    visit::{IntoNodeReferences, NodeIndexable, NodeRef},
    Direction,
};

/// Structure responsible for converting one [`DepGraph`] into an [`SPDG`].
///
/// Intended usage is to call [`Self::new_with_flowistry`] to initialize, then
/// [`Self::make_spdg`] to convert.
pub struct GraphConverter<'tcx, 'a, C> {
    // Immutable information
    /// The parent generator
    generator: &'a SPDGGenerator<'tcx>,
    /// Information about the function this PDG belongs to
    target: FnToAnalyze,
    /// The flowistry graph we are converting
    dep_graph: Rc<DepGraph<'tcx>>,
    /// Same as the ID stored in self.target, but as a local def id
    local_def_id: LocalDefId,

    // Mutable fields
    /// Where we write every [`DefId`] we encounter into.
    known_def_ids: &'a mut C,
    /// A map of which nodes are of which (marked) type. We build this up during
    /// conversion.
    types: HashMap<Node, Vec<DefId>>,
    /// Mapping from old node indices to new node indices. Use
    /// [`Self::register_node`] to insert and [`Self::new_node_for`] to query.
    index_map: Box<[Node]>,
    /// The converted graph we are creating
    spdg: SPDGImpl,
    marker_assignments: HashMap<Node, HashSet<Identifier>>,
}
impl<'a, 'tcx, C: Extend<DefId>> GraphConverter<'tcx, 'a, C> {
    /// Initialize a new converter by creating an initial PDG using flowistry.
    pub fn new_with_flowistry(
        generator: &'a SPDGGenerator<'tcx>,
        known_def_ids: &'a mut C,
        target: FnToAnalyze,
    ) -> Result<Self> {
        let local_def_id = target.def_id.expect_local();
        let start = Instant::now();
        let dep_graph = Rc::new(Self::create_flowistry_graph(generator, local_def_id)?);
        generator
            .stats
            .record_timed(TimedStat::Flowistry, start.elapsed());

        if generator.opts.dbg().dump_flowistry_pdg() {
            dep_graph.generate_graphviz(format!(
                "{}.flowistry-pdg.pdf",
                generator.tcx.def_path_str(target.def_id)
            ))?
        }

        Ok(Self {
            generator,
            known_def_ids,
            target,
            index_map: vec![default_index(); dep_graph.as_ref().graph.node_bound()].into(),
            dep_graph,
            local_def_id,
            types: Default::default(),
            spdg: Default::default(),
            marker_assignments: Default::default(),
        })
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.generator.tcx
    }

    fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        &self.generator.marker_ctx
    }

    /// Is the top-level function (entrypoint) an `async fn`
    fn entrypoint_is_async(&self) -> bool {
        self.tcx().asyncness(self.local_def_id).is_async()
            || is_async_trait_fn(
                self.tcx(),
                self.local_def_id.to_def_id(),
                &self.tcx().body_for_def_id(self.local_def_id).unwrap().body,
            )
    }

    /// Find the statement at this location or fail.
    fn expect_stmt_at(
        &self,
        loc: GlobalLocation,
    ) -> Either<&'tcx mir::Statement<'tcx>, &'tcx mir::Terminator<'tcx>> {
        let body = &self.tcx().body_for_def_id(loc.function).unwrap().body;
        let RichLocation::Location(loc) = loc.location else {
            unreachable!();
        };
        body.stmt_at(loc)
    }

    /// Insert this node into the converted graph, return it's auto-assigned id
    /// and register it as corresponding to `old` in the initial graph. Fails if
    /// there is already a node registered as corresponding to `old`.
    fn register_node(&mut self, old: Node, new: NodeInfo) -> Node {
        let new_node = self.spdg.add_node(new);
        let r = &mut self.index_map[old.index()];
        assert_eq!(*r, default_index());
        *r = new_node;
        new_node
    }

    /// Get the id of the new node that was registered for this old node.
    fn new_node_for(&self, old: Node) -> Node {
        let res = self.index_map[old.index()];
        assert_ne!(res, default_index());
        res
    }

    fn register_markers(&mut self, node: Node, markers: impl IntoIterator<Item = Identifier>) {
        let mut markers = markers.into_iter().peekable();

        if !markers.peek().is_none() {
            self.marker_assignments
                .entry(node)
                .or_default()
                .extend(markers);
        }
    }

    /// Find direct annotations on this node and register them in the marker map.
    fn node_annotations(&mut self, old_node: Node, weight: &DepNode<'tcx>) {
        let leaf_loc = weight.at.leaf();
        let node = self.new_node_for(old_node);

        let body = &self.tcx().body_for_def_id(leaf_loc.function).unwrap().body;

        let graph = self.dep_graph.clone();

        match leaf_loc.location {
            RichLocation::Start
                if matches!(body.local_kind(weight.place.local), mir::LocalKind::Arg) =>
            {
                let function_id = leaf_loc.function.to_def_id();
                let arg_num = weight.place.local.as_u32() - 1;
                self.known_def_ids.extend(Some(function_id));

                self.register_annotations_for_function(node, function_id, |ann| {
                    ann.refinement
                        .on_argument()
                        .contains(arg_num as u32)
                        .unwrap()
                });
            }
            RichLocation::End if weight.place.local == mir::RETURN_PLACE => {
                let function_id = leaf_loc.function.to_def_id();
                self.known_def_ids.extend(Some(function_id));
                self.register_annotations_for_function(node, function_id, |ann| {
                    ann.refinement.on_return()
                });
            }
            RichLocation::Location(loc) => {
                let stmt_at_loc = body.stmt_at(loc);
                if let crate::Either::Right(
                    term @ mir::Terminator {
                        kind: mir::TerminatorKind::Call { destination, .. },
                        ..
                    },
                ) = stmt_at_loc
                {
                    let (fun, ..) = term.as_fn_and_args(self.tcx()).unwrap();
                    self.known_def_ids.extend(Some(fun));

                    // Question: Could a function with no input produce an
                    // output that has aliases? E.g. could some place, where the
                    // local portion isn't the local from the destination of
                    // this function call be affected/modified by this call? If
                    // so, that location would also need to have this marker
                    // attached
                    let needs_return_marker_registration = weight.place.local == destination.local
                        || graph
                            .graph
                            .edges_directed(old_node, Direction::Incoming)
                            .any(|e| {
                                if weight.at != e.weight().at {
                                    // Incoming edges are either from our operation or from control flow
                                    let at = e.weight().at;
                                    debug_assert!(
                                        at.leaf().function == leaf_loc.function
                                            && if let RichLocation::Location(loc) =
                                                at.leaf().location
                                            {
                                                matches!(
                                                    body.stmt_at(loc),
                                                    Either::Right(mir::Terminator {
                                                        kind: mir::TerminatorKind::SwitchInt { .. },
                                                        ..
                                                    })
                                                )
                                            } else {
                                                false
                                            }
                                    );
                                    false
                                } else {
                                    e.weight().target_use.is_return()
                                }
                            });

                    if needs_return_marker_registration {
                        self.register_annotations_for_function(node, fun, |ann| {
                            ann.refinement.on_return()
                        });
                    }

                    // This is not ideal. We have to do extra work here and fetch
                    // the `at` location for each outgoing edge, because their
                    // operations happen on a different function.
                    for e in graph.graph.edges_directed(old_node, Direction::Outgoing) {
                        let SourceUse::Argument(arg) = e.weight().source_use else {
                            continue;
                        };
                        self.register_annotations_for_function(node, fun, |ann| {
                            ann.refinement.on_argument().contains(arg as u32).unwrap()
                        })
                    }
                }
            }
            _ => (),
        }
    }

    /// Reconstruct the type for the data this node represents.
    fn determine_place_type(
        &self,
        at: CallString,
        place: mir::Place<'tcx>,
    ) -> mir::tcx::PlaceTy<'tcx> {
        let tcx = self.tcx();
        let locations = at.iter_from_root().collect::<Vec<_>>();
        let (last, mut rest) = locations.split_last().unwrap();

        if self.entrypoint_is_async() {
            let (first, tail) = rest.split_first().unwrap();
            // The body of a top-level `async` function binds a closure to the
            // return place `_0`. Here we expect are looking at the statement
            // that does this binding.
            assert!(self.expect_stmt_at(*first).is_left());
            rest = tail;
        }

        // So actually we're going to check the base place only, because
        // Flowistry sometimes tracks subplaces instead but we want the marker
        // from the base place.
        let place = if self.entrypoint_is_async() && place.local.as_u32() == 1 && rest.len() == 1 {
            assert!(place.projection.len() >= 1, "{place:?} at {rest:?}");
            // in the case of targeting the top-level async closure (e.g. async args)
            // we'll keep the first projection.
            mir::Place {
                local: place.local,
                projection: self.tcx().mk_place_elems(&place.projection[..1]),
            }
        } else {
            place.local.into()
        };

        fn normalize<'a, 'tcx, I: ty::TypeFoldable<TyCtxt<'tcx>> + Clone>(
            resolution: FnResolution<'tcx>,
            tcx: TyCtxt<'tcx>,
            f: &'a I,
        ) -> Cow<'a, I> {
            match resolution {
                FnResolution::Final(instance) => {
                    Cow::Owned(instance.subst_mir_and_normalize_erasing_regions(
                        tcx,
                        tcx.param_env(resolution.def_id()),
                        ty::EarlyBinder::bind(tcx.erase_regions(f.clone())),
                    ))
                }
                FnResolution::Partial(_) => Cow::Borrowed(f),
            }
        }

        let resolution = rest.iter().fold(
            FnResolution::Partial(self.local_def_id.to_def_id()),
            |resolution, caller| {
                let base_stmt = self.expect_stmt_at(*caller);
                let normalized = map_either(
                    base_stmt,
                    |stmt| normalize(resolution, tcx, stmt),
                    |term| normalize(resolution, tcx, term),
                );
                match normalized {
                    Either::Right(term) => term.as_ref().as_instance_and_args(tcx).unwrap().0,
                    Either::Left(stmt) => {
                        if let Some((def_id, generics)) = match_async_trait_assign(stmt.as_ref()) {
                            try_resolve_function(
                                tcx,
                                def_id,
                                tcx.param_env(resolution.def_id()),
                                generics,
                            )
                        } else {
                            unreachable!("{stmt:?}\nat {caller} in {}", at)
                        }
                    }
                }
            },
        );
        // Thread through each caller to recover generic arguments
        let body = tcx.body_for_def_id(last.function).unwrap();
        let raw_ty = place.ty(&body.body, tcx);
        match resolution {
            FnResolution::Partial(_) => raw_ty,
            FnResolution::Final(instance) => instance.subst_mir_and_normalize_erasing_regions(
                tcx,
                ty::ParamEnv::reveal_all(),
                ty::EarlyBinder::bind(tcx.erase_regions(raw_ty)),
            ),
        }
    }

    /// Fetch annotations item identified by this `id`.
    ///
    /// The callback is used to filter out annotations where the "refinement"
    /// doesn't match. The idea is that the caller of this function knows
    /// whether they are looking for annotations on an argument or return of a
    /// function identified by this `id` or on a type and the callback should be
    /// used to enforce this.
    fn register_annotations_for_function(
        &mut self,
        node: Node,
        function: DefId,
        mut filter: impl FnMut(&MarkerAnnotation) -> bool,
    ) {
        let parent = get_parent(self.tcx(), function);
        let marker_ctx = self.marker_ctx().clone();
        self.register_markers(
            node,
            marker_ctx
                .combined_markers(function)
                .chain(
                    parent
                        .into_iter()
                        .flat_map(|parent| marker_ctx.combined_markers(parent)),
                )
                .filter(|ann| filter(ann))
                .map(|ann| ann.marker),
        );
        self.known_def_ids.extend(parent);
    }

    /// Check if this node is of a marked type and register that type.
    fn handle_node_types(&mut self, old_node: Node, weight: &DepNode<'tcx>) {
        let i = self.new_node_for(old_node);

        let is_controller_argument =
            matches!(self.try_as_root(weight.at), Some(l) if l.location == RichLocation::Start);

        if self
            .dep_graph
            .graph
            .edges_directed(old_node, Direction::Incoming)
            .any(|e| e.weight().target_use.is_return() && e.weight().source_use.is_argument())
        {
            assert!(
                weight.place.projection.is_empty(),
                "{:?} at {} has projection",
                weight.place,
                weight.at
            );
        } else if !is_controller_argument {
            return;
        }

        let place_ty = self.determine_place_type(weight.at, weight.place);

        let is_external_call_source = weight.at.leaf().location != RichLocation::End;

        let node_types = self.type_is_marked(place_ty, is_external_call_source);
        self.known_def_ids.extend(node_types.iter().copied());
        let tcx = self.tcx();
        if !node_types.is_empty() {
            self.types
                .entry(i)
                .or_default()
                .extend(node_types.iter().filter(|t| match tcx.def_kind(*t) {
                    def::DefKind::Generator => false,
                    kind => !kind.is_fn_like(),
                }))
        }
    }

    /// Create an initial flowistry graph for the function identified by
    /// `local_def_id`.
    fn create_flowistry_graph(
        generator: &SPDGGenerator<'tcx>,
        local_def_id: LocalDefId,
    ) -> Result<DepGraph<'tcx>> {
        let tcx = generator.tcx;
        let opts = generator.opts;
        let judge =
            inline_judge::InlineJudge::new(generator.marker_ctx.clone(), tcx, opts.anactrl());
        let stat_wrap = generator.stats.clone();
        let params = PdgParams::new(tcx, local_def_id).with_call_change_callback(move |info| {
            let mut changes = CallChanges::default();

            let mut skip = true;

            if is_non_default_trait_method(tcx, info.callee.def_id()).is_some() {
                tcx.sess.span_warn(
                    tcx.def_span(info.callee.def_id()),
                    "Skipping analysis of unresolvable trait method.",
                );
            } else if judge.should_inline(&info) {
                skip = false;
            };

            if skip {
                changes = changes.with_skip(Skip);
            } else {
                stat_wrap.record_inlining(tcx, info.callee.def_id().expect_local(), info.is_cached)
            }
            changes
        });
        if opts.dbg().dump_mir() {
            let mut file = std::fs::File::create(format!(
                "{}.mir",
                tcx.def_path_str(local_def_id.to_def_id())
            ))?;
            mir::pretty::write_mir_fn(
                tcx,
                &tcx.body_for_def_id_default_policy(local_def_id)
                    .ok_or_else(|| anyhow!("Body not found"))?
                    .body,
                &mut |_, _| Ok(()),
                &mut file,
            )?
        }

        Ok(flowistry_pdg_construction::compute_pdg(params))
    }

    /// Consume the generator and compile the [`SPDG`].
    pub fn make_spdg(mut self) -> SPDG {
        let start = Instant::now();
        self.make_spdg_impl();
        let arguments = self.determine_arguments();
        let return_ = self.determine_return();
        self.generator
            .stats
            .record_timed(TimedStat::Conversion, start.elapsed());
        SPDG {
            path: path_for_item(self.local_def_id.to_def_id(), self.tcx()),
            graph: self.spdg,
            id: self.local_def_id,
            name: Identifier::new(self.target.name()),
            arguments,
            markers: self
                .marker_assignments
                .into_iter()
                .map(|(k, v)| (k, v.into_iter().collect()))
                .collect(),
            return_,
            type_assigns: self
                .types
                .into_iter()
                .map(|(k, v)| (k, Types(v.into())))
                .collect(),
        }
    }

    /// This initializes the fields `spdg` and `index_map` and should be called first
    fn make_spdg_impl(&mut self) {
        use petgraph::prelude::*;
        let g_ref = self.dep_graph.clone();
        let input = &g_ref.graph;
        let tcx = self.tcx();

        for (i, weight) in input.node_references() {
            let at = weight.at.leaf();
            let body = &tcx.body_for_def_id(at.function).unwrap().body;

            let node_span = body.local_decls[weight.place.local].source_info.span;
            let new_idx = self.register_node(
                i,
                NodeInfo {
                    at: weight.at,
                    description: format!("{:?}", weight.place),
                    span: src_loc_for_span(node_span, tcx),
                },
            );
            trace!(
                "Node {new_idx:?}\n  description: {:?}\n  at: {at}\n  stmt: {}",
                weight.place,
                match at.location {
                    RichLocation::Location(loc) => {
                        match body.stmt_at(loc) {
                            Either::Left(s) => format!("{:?}", s.kind),
                            Either::Right(s) => format!("{:?}", s.kind),
                        }
                    }
                    RichLocation::End => "end".to_string(),
                    RichLocation::Start => "start".to_string(),
                }
            );
            self.node_annotations(i, weight);

            self.handle_node_types(i, weight);
        }

        for e in input.edge_references() {
            let DepEdge {
                kind,
                at,
                source_use,
                target_use,
            } = *e.weight();
            self.spdg.add_edge(
                self.new_node_for(e.source()),
                self.new_node_for(e.target()),
                EdgeInfo {
                    at,
                    kind: match kind {
                        DepEdgeKind::Control => EdgeKind::Control,
                        DepEdgeKind::Data => EdgeKind::Data,
                    },
                    source_use,
                    target_use,
                },
            );
        }
    }

    /// Return the (sub)types of this type that are marked.
    fn type_is_marked(&self, typ: mir::tcx::PlaceTy<'tcx>, walk: bool) -> Vec<TypeId> {
        if walk {
            self.marker_ctx()
                .all_type_markers(typ.ty)
                .map(|t| t.1 .1)
                .collect()
        } else {
            self.marker_ctx()
                .type_has_surface_markers(typ.ty)
                .into_iter()
                .collect()
        }
    }

    /// Similar to `CallString::is_at_root`, but takes into account top-level
    /// async functions
    fn try_as_root(&self, at: CallString) -> Option<GlobalLocation> {
        if self.entrypoint_is_async() && at.len() == 2 {
            at.iter_from_root().nth(1)
        } else if at.is_at_root() {
            Some(at.leaf())
        } else {
            None
        }
    }

    /// Try to find the node corresponding to the values returned from this
    /// controller.
    ///
    /// TODO: Include mutable inputs
    fn determine_return(&self) -> Box<[Node]> {
        // In async functions
        let return_candidates = self
            .spdg
            .node_references()
            .filter(|n| {
                let weight = n.weight();
                let at = weight.at;
                matches!(self.try_as_root(at), Some(l) if l.location == RichLocation::End)
            })
            .map(|n| n.id())
            .collect::<Box<[_]>>();
        if return_candidates.len() != 1 {
            warn!("Found many candidates for the return: {return_candidates:?}.");
        }
        return_candidates
    }

    /// Determine the set if nodes corresponding to the inputs to the
    /// entrypoint. The order is guaranteed to be the same as the source-level
    /// function declaration.
    fn determine_arguments(&self) -> Box<[Node]> {
        let mut g_nodes: Vec<_> = self
            .dep_graph
            .graph
            .node_references()
            .filter(|n| {
                let at = n.weight().at;
                let is_candidate =
                    matches!(self.try_as_root(at), Some(l) if l.location == RichLocation::Start);
                is_candidate
            })
            .collect();

        g_nodes.sort_by_key(|(_, i)| i.place.local);

        g_nodes
            .into_iter()
            .map(|n| self.new_node_for(n.id()))
            .collect()
    }
}

/// If `did` is a method of an `impl` of a trait, then return the `DefId` that
/// refers to the method on the trait definition.
fn get_parent(tcx: TyCtxt, did: DefId) -> Option<DefId> {
    let ident = tcx.opt_item_ident(did)?;
    let kind = match tcx.def_kind(did) {
        kind if kind.is_fn_like() => ty::AssocKind::Fn,
        // todo allow constants and types also
        _ => return None,
    };
    let r#impl = tcx.impl_of_method(did)?;
    let r#trait = tcx.trait_id_of_impl(r#impl)?;
    let id = tcx
        .associated_items(r#trait)
        .find_by_name_and_kind(tcx, ident, kind, r#trait)?
        .def_id;
    Some(id)
}
