use crate::{
    ana::inline_judge::InlineJudge,
    ann::MarkerAnnotation,
    desc::*,
    discover::FnToAnalyze,
    rust::{hir::def, *},
    stats::TimedStat,
    utils::*,
    DefId, HashMap, HashSet, MarkerCtx,
};
use flowistry::mir::placeinfo::PlaceInfo;
use flowistry_pdg::SourceUse;
use paralegal_spdg::{Node, SPDGStats};
use rustc_utils::cache::Cache;

use std::{
    cell::RefCell,
    fmt::Display,
    rc::Rc,
    time::{Duration, Instant},
};

use self::call_string_resolver::CallStringResolver;

use super::{default_index, path_for_item, src_loc_for_span, SPDGGenerator};
use anyhow::{anyhow, Result};
use either::Either;
use flowistry_pdg_construction::{
    graph::{DepEdge, DepEdgeKind, DepGraph, DepNode},
    is_async_trait_fn, match_async_trait_assign, CallChangeCallback, CallChanges, CallInfo,
    InlineMissReason, PdgParams,
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
    call_string_resolver: call_string_resolver::CallStringResolver<'tcx>,
    stats: SPDGStats,
    analyzed_functions: HashSet<LocalDefId>,
    place_info_cache: PlaceInfoCache<'tcx>,
}

pub type PlaceInfoCache<'tcx> = Rc<Cache<LocalDefId, PlaceInfo<'tcx>>>;

impl<'a, 'tcx, C: Extend<DefId>> GraphConverter<'tcx, 'a, C> {
    /// Initialize a new converter by creating an initial PDG using flowistry.
    pub fn new_with_flowistry(
        generator: &'a SPDGGenerator<'tcx>,
        known_def_ids: &'a mut C,
        target: FnToAnalyze,
        place_info_cache: PlaceInfoCache<'tcx>,
    ) -> Result<Self> {
        let local_def_id = target.def_id.expect_local();
        let start = Instant::now();
        let (dep_graph, stats, analyzed_functions) =
            Self::create_flowistry_graph(generator, local_def_id)?;
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
            index_map: vec![default_index(); dep_graph.graph.node_bound()].into(),
            dep_graph: dep_graph.into(),
            local_def_id,
            types: Default::default(),
            spdg: Default::default(),
            marker_assignments: Default::default(),
            call_string_resolver: CallStringResolver::new(generator.tcx, local_def_id),
            stats,
            analyzed_functions,
            place_info_cache,
        })
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.generator.tcx
    }

    fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        &self.generator.marker_ctx()
    }

    /// Is the top-level function (entrypoint) an `async fn`
    fn entrypoint_is_async(&self) -> bool {
        entrypoint_is_async(self.tcx(), self.local_def_id)
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

        if markers.peek().is_some() {
            self.marker_assignments
                .entry(node)
                .or_default()
                .extend(markers);
        }
    }

    fn place_info(&self, def_id: LocalDefId) -> &PlaceInfo<'tcx> {
        self.place_info_cache.get(def_id, |_| {
            PlaceInfo::build(
                self.tcx(),
                def_id.to_def_id(),
                &self.tcx().body_for_def_id(def_id).unwrap(),
            )
        })
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
                    ann.refinement.on_argument().contains(arg_num).unwrap()
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
                    let res = self.call_string_resolver.resolve(weight.at);
                    let (fun, ..) = res
                        .try_monomorphize(self.tcx(), self.tcx().param_env(res.def_id()), term)
                        .as_instance_and_args(self.tcx())
                        .unwrap();
                    self.known_def_ids.extend(Some(fun.def_id()));

                    // Question: Could a function with no input produce an
                    // output that has aliases? E.g. could some place, where the
                    // local portion isn't the local from the destination of
                    // this function call be affected/modified by this call? If
                    // so, that location would also need to have this marker
                    // attached
                    let needs_return_markers = weight.place.local == destination.local
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

                    if needs_return_markers {
                        self.register_annotations_for_function(node, fun.def_id(), |ann| {
                            ann.refinement.on_return()
                        });
                    }

                    for e in graph.graph.edges_directed(old_node, Direction::Outgoing) {
                        let SourceUse::Argument(arg) = e.weight().source_use else {
                            continue;
                        };
                        self.register_annotations_for_function(node, fun.def_id(), |ann| {
                            ann.refinement.on_argument().contains(arg as u32).unwrap()
                        });
                    }

                    // Overapproximation of markers for fixed inlining depths.
                    // If the skipped inlining a function because of the
                    // inlining depth restriction we overapproximate how the
                    // reachable markers may have affected each argument and
                    // return by attaching each reachable marker to each
                    // argument and the return.
                    //
                    // Explanation of each `&&`ed part of this condition in
                    // order:
                    //
                    // - Optimization. If the inlining depth is not fixed, none
                    //   of the following conditions will be true and this one
                    //   is cheap to check.
                    // - If the function is marked we currently don't propagate
                    //   other reachable markers outside
                    // - If the function was inlined, the PDG will cover the
                    //   markers so we don't have to.
                    if self.generator.opts.anactrl().inlining_depth().is_fixed()
                        && !self.marker_ctx().is_marked(fun.def_id())
                        && !self.generator.inline_judge.should_inline(&CallInfo {
                            call_string: weight.at,
                            callee: fun,
                            is_cached: true,
                        })
                    {
                        let mctx = self.marker_ctx().clone();
                        let markers = mctx.get_reachable_markers(fun);
                        self.register_markers(node, markers.iter().copied())
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
        place: mir::PlaceRef<'tcx>,
    ) -> Option<mir::tcx::PlaceTy<'tcx>> {
        let tcx = self.tcx();
        let locations = at.iter_from_root().collect::<Vec<_>>();
        let (last, mut rest) = locations.split_last().unwrap();

        if self.entrypoint_is_async() {
            let (first, tail) = rest.split_first().unwrap();
            // The body of a top-level `async` function binds a closure to the
            // return place `_0`. Here we expect are looking at the statement
            // that does this binding.
            assert!(expect_stmt_at(self.tcx(), *first).is_left());
            rest = tail;
        }

        // So actually we're going to check the base place only, because
        // Flowistry sometimes tracks subplaces instead but we want the marker
        // from the base place.
        let place = if self.entrypoint_is_async() && place.local.as_u32() == 1 && rest.len() == 1 {
            if place.projection.len() < 1 {
                return None;
            }
            // in the case of targeting the top-level async closure (e.g. async args)
            // we'll keep the first projection.
            mir::Place {
                local: place.local,
                projection: self.tcx().mk_place_elems(&place.projection[..1]),
            }
        } else {
            place.local.into()
        };

        let resolution = self.call_string_resolver.resolve(at);

        // Thread through each caller to recover generic arguments
        let body = tcx.body_for_def_id(last.function).unwrap();
        let raw_ty = place.ty(&body.body, tcx);
        Some(*resolution.try_monomorphize(tcx, ty::ParamEnv::reveal_all(), &raw_ty))
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

        let place_ty = self
            .determine_place_type(weight.at, weight.place.as_ref())
            .unwrap();
        let place_info = self.place_info(weight.at.leaf().function);
        let deep = !place_info.children(weight.place).is_empty();
        let mut node_types = self.type_is_marked(place_ty, deep).collect::<HashSet<_>>();
        for (p, _) in weight.place.iter_projections() {
            if let Some(place_ty) = self.determine_place_type(weight.at, p) {
                node_types.extend(self.type_is_marked(place_ty, false));
            }
        }
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
    ) -> Result<(DepGraph<'tcx>, SPDGStats, HashSet<LocalDefId>)> {
        let tcx = generator.tcx;
        let opts = generator.opts;
        let stat_wrap = Rc::new(RefCell::new((
            SPDGStats {
                unique_functions: 0,
                unique_locs: 0,
                analyzed_functions: 0,
                analyzed_locs: 0,
                inlinings_performed: 0,
                construction_time: Duration::ZERO,
                conversion_time: Duration::ZERO,
            },
            Default::default(),
        )));
        // Make sure we count outselves
        record_inlining(&stat_wrap, tcx, local_def_id, false);
        let stat_wrap_copy = stat_wrap.clone();
        let judge = generator.inline_judge.clone();
        struct MyCallback<'tcx> {
            judge: InlineJudge<'tcx>,
            stat_wrap: Rc<RefCell<(SPDGStats, HashSet<LocalDefId>)>>,
            tcx: TyCtxt<'tcx>,
        }

        impl<'tcx> CallChangeCallback<'tcx> for MyCallback<'tcx> {
            fn on_inline(&self, info: CallInfo<'tcx>) -> CallChanges<'tcx> {
                let mut changes = CallChanges::default();

                let mut skip = true;

                if is_non_default_trait_method(self.tcx, info.callee.def_id()).is_some() {
                    self.tcx.sess.span_warn(
                        self.tcx.def_span(info.callee.def_id()),
                        "Skipping analysis of unresolvable trait method.",
                    );
                } else if self.judge.should_inline(&info) {
                    skip = false;
                };

                if skip {
                    changes = changes.with_skip(Skip);
                } else {
                    record_inlining(
                        &self.stat_wrap,
                        self.tcx,
                        info.callee.def_id().expect_local(),
                        info.is_cached,
                    )
                }
                changes
            }

            fn on_inline_miss(
                &self,
                resolution: FnResolution<'tcx>,
                loc: Location,
                parent: FnResolution<'tcx>,
                call_string: Option<CallString>,
                reason: InlineMissReason,
            ) {
                let body = self
                    .tcx
                    .body_for_def_id(parent.def_id().expect_local())
                    .unwrap();
                let span = body
                    .body
                    .stmt_at(loc)
                    .either(|s| s.source_info.span, |t| t.source_info.span);
                let markers_reachable = self.judge.marker_ctx().get_reachable_markers(resolution);
                self.tcx.sess.span_err(
                    span,
                    format!(
                        "Could not inline this function call in {:?}, at {} because {reason:?}. {}",
                        parent.def_id(),
                        call_string.map_or("root".to_owned(), |c| c.to_string()),
                        Print(|f| if markers_reachable.is_empty() {
                            f.write_str("No markers are reachable")
                        } else {
                            f.write_str("Markers ")?;
                            write_sep(f, ", ", markers_reachable.iter(), Display::fmt)?;
                            f.write_str(" are reachable")
                        })
                    ),
                );
            }
        }
        let params = PdgParams::new(tcx, local_def_id)
            .with_call_change_callback(MyCallback {
                judge,
                stat_wrap,
                tcx,
            })
            .with_dump_mir(generator.opts.dbg().dump_mir());

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
        let flowistry_time = Instant::now();
        let pdg = flowistry_pdg_construction::compute_pdg(params);
        let (mut stats, ana_fnset) = Rc::into_inner(stat_wrap_copy).unwrap().into_inner();
        stats.construction_time = flowistry_time.elapsed();

        Ok((pdg, stats, ana_fnset))
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
        self.stats.conversion_time = start.elapsed();
        let tcx = self.tcx();
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
            statistics: self.stats,
            analyzed_spans: self
                .analyzed_functions
                .into_iter()
                .map(|f| {
                    let span = tcx.body_for_def_id(f).unwrap().body.span;
                    (f, src_loc_for_span(span, tcx))
                })
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
    fn type_is_marked(
        &'a self,
        typ: mir::tcx::PlaceTy<'tcx>,
        deep: bool,
    ) -> impl Iterator<Item = TypeId> + 'a {
        if deep {
            Either::Left(self.marker_ctx().deep_type_markers(typ.ty).iter().copied())
        } else {
            Either::Right(self.marker_ctx().shallow_type_markers(typ.ty))
        }
        .map(|(d, _)| d)

        //     self.marker_ctx()
        //         .all_type_markers(typ.ty)
        //         .map(|t| t.1 .1)
        //         .collect()
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

fn record_inlining(
    tracker: &Rc<RefCell<(SPDGStats, HashSet<LocalDefId>)>>,
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
    is_in_cache: bool,
) {
    let mut borrow = tracker.borrow_mut();
    let (stats, loc_set) = &mut *borrow;
    let src_map = tcx.sess.source_map();
    let span = tcx.body_for_def_id(def_id).unwrap().body.span;
    let (_, start_line, _, end_line, _) = src_map.span_to_location_info(span);
    let body_lines = (end_line - start_line) as u32;
    stats.inlinings_performed += 1;
    if loc_set.insert(def_id) {
        stats.unique_functions += 1;
        stats.unique_locs += body_lines;
    }
    if !is_in_cache {
        stats.analyzed_functions += 1;
        stats.analyzed_locs += body_lines;
    }
}

/// Find the statement at this location or fail.
fn expect_stmt_at<'tcx>(
    tcx: TyCtxt<'tcx>,
    loc: GlobalLocation,
) -> Either<&'tcx mir::Statement<'tcx>, &'tcx mir::Terminator<'tcx>> {
    let body = &tcx.body_for_def_id(loc.function).unwrap().body;
    let RichLocation::Location(loc) = loc.location else {
        unreachable!();
    };
    body.stmt_at(loc)
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

fn entrypoint_is_async(tcx: TyCtxt, local_def_id: LocalDefId) -> bool {
    tcx.asyncness(local_def_id).is_async()
        || is_async_trait_fn(
            tcx,
            local_def_id.to_def_id(),
            &tcx.body_for_def_id(local_def_id).unwrap().body,
        )
}

mod call_string_resolver {
    //! Resolution of [`CallString`]s to [`FnResolution`]s.
    //!
    //! This is a separate mod so that we can use encapsulation to preserve the
    //! internal invariants of the resolver.

    use flowistry_pdg::{rustc_portable::LocalDefId, CallString};
    use flowistry_pdg_construction::{try_resolve_function, FnResolution};
    use rustc_utils::cache::Cache;

    use crate::{Either, TyCtxt};

    use super::{map_either, match_async_trait_assign, AsFnAndArgs};

    /// Cached resolution of [`CallString`]s to [`FnResolution`]s.
    ///
    /// Only valid for a single controller. Each controller should initialize a
    /// new resolver.
    pub struct CallStringResolver<'tcx> {
        cache: Cache<CallString, FnResolution<'tcx>>,
        tcx: TyCtxt<'tcx>,
        entrypoint_is_async: bool,
    }

    impl<'tcx> CallStringResolver<'tcx> {
        /// Tries to resolve to the monomophized function in which this call
        /// site exists. That is to say that `return.def_id() ==
        /// cs.leaf().function`.
        ///
        /// Unlike `Self::resolve_internal` this can be called on any valid
        /// [`CallString`].
        pub fn resolve(&self, cs: CallString) -> FnResolution<'tcx> {
            let (this, opt_prior_loc) = cs.pop();
            if let Some(prior_loc) = opt_prior_loc {
                if prior_loc.len() == 1 && self.entrypoint_is_async {
                    FnResolution::Partial(this.function.to_def_id())
                } else {
                    self.resolve_internal(prior_loc)
                }
            } else {
                FnResolution::Partial(this.function.to_def_id())
            }
        }

        pub fn new(tcx: TyCtxt<'tcx>, entrypoint: LocalDefId) -> Self {
            Self {
                cache: Default::default(),
                tcx,
                entrypoint_is_async: super::entrypoint_is_async(tcx, entrypoint),
            }
        }

        /// This resolves the monomorphized function *being called at* this call
        /// site.
        ///
        /// This function is internal because it panics if `cs.leaf().location`
        /// is not either a function call or a statement where an async closure
        /// is created and assigned.
        fn resolve_internal(&self, cs: CallString) -> FnResolution<'tcx> {
            *self.cache.get(cs, |_| {
                let this = cs.leaf();
                let prior = self.resolve(cs);

                let tcx = self.tcx;

                let base_stmt = super::expect_stmt_at(tcx, this);
                let param_env = tcx.param_env_reveal_all_normalized(prior.def_id());
                let normalized = map_either(
                    base_stmt,
                    |stmt| prior.try_monomorphize(tcx, param_env, stmt),
                    |term| prior.try_monomorphize(tcx, param_env, term),
                );
                let res = match normalized {
                    Either::Right(term) => term.as_ref().as_instance_and_args(tcx).unwrap().0,
                    Either::Left(stmt) => {
                        let (def_id, generics) = match_async_trait_assign(stmt.as_ref()).unwrap();
                        try_resolve_function(tcx, def_id, param_env, generics)
                    }
                };
                res
            })
        }
    }
}
