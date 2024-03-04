//! Data-and control flow analyzer and inliner.
//!
//! Analysis starts with the construction of [`SPDGGenerator`] from a
//! [`CollectingVisitor`](crate::discover::CollectingVisitor) and then calling
//! [`analyze`](SPDGGenerator::analyze).

use super::discover::FnToAnalyze;
use crate::{
    ann::{Annotation, MarkerAnnotation},
    desc::*,
    rust::{hir::def, *},
    utils::*,
    DefId, HashMap, HashSet, LogLevelConfig, MarkerCtx, Symbol,
};
use paralegal_spdg::Node;

use std::borrow::Cow;
use std::rc::Rc;

use anyhow::{anyhow, Result};
use either::Either;
use flowistry::pdg::{
    graph::{DepEdgeKind, DepGraph, DepNode},
    is_async_trait_fn, CallChanges,
    SkipCall::Skip,
};
use itertools::Itertools;
use petgraph::visit::{GraphBase, IntoNodeReferences, NodeIndexable, NodeRef};
use rustc_span::{FileNameDisplayPreference, Span};

mod inline_judge;

/// Read-only database of information the analysis needs.
///
/// [`Self::analyze`] serves as the main entrypoint to SPDG generation.
pub struct SPDGGenerator<'tcx> {
    pub marker_ctx: MarkerCtx<'tcx>,
    pub opts: &'static crate::Args,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> SPDGGenerator<'tcx> {
    pub fn new(marker_ctx: MarkerCtx<'tcx>, opts: &'static crate::Args, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            marker_ctx,
            opts,
            tcx,
        }
    }

    /// Perform the analysis for one `#[paralegal_flow::analyze]` annotated function and
    /// return the representation suitable for emitting into Forge.
    ///
    /// Main work for a single target is performed by [`GraphConverter`].
    fn handle_target(
        &self,
        //_hash_verifications: &mut HashVerifications,
        target: FnToAnalyze,
        known_def_ids: &mut impl Extend<DefId>,
    ) -> Result<(Endpoint, SPDG)> {
        debug!("Handling target {}", target.name());
        let local_def_id = target.def_id.expect_local();

        let converter = GraphConverter::new_with_flowistry(self, known_def_ids, target)?;
        let spdg = converter.make_spdg();

        Ok((local_def_id, spdg))
    }

    /// Main analysis driver. Essentially just calls [`Self::handle_target`]
    /// once for every function in `self.functions_to_analyze` after doing some
    /// other setup necessary for the flow graph creation.
    ///
    /// Should only be called after the visit.
    pub fn analyze(&self, targets: Vec<FnToAnalyze>) -> Result<ProgramDescription> {
        if let LogLevelConfig::Targeted(s) = self.opts.direct_debug() {
            assert!(
                targets.iter().any(|target| target.name().as_str() == s),
                "Debug output option specified a specific target '{s}', but no such target was found in [{}]",
                Print(|f: &mut std::fmt::Formatter<'_>| {
                    write_sep(f, ", ", targets.iter(), |t, f| {
                        f.write_str(t.name().as_str())
                    })
                })
            )
        }

        let mut known_def_ids = HashSet::new();

        targets
            .into_iter()
            .map(|desc| {
                let target_name = desc.name();
                with_reset_level_if_target(self.opts, target_name, || {
                    self.handle_target(
                        //hash_verifications,
                        desc,
                        &mut known_def_ids,
                    )
                })
            })
            .collect::<Result<HashMap<Endpoint, SPDG>>>()
            .map(|controllers| self.make_program_description(controllers, &known_def_ids))
    }

    /// Given the PDGs and a record of all [`DefId`]s we've seen, compile
    /// auxillary information the policies will need into the artifact to be
    /// emitted.
    fn make_program_description(
        &self,
        controllers: HashMap<Endpoint, SPDG>,
        known_def_ids: &HashSet<DefId>,
    ) -> ProgramDescription {
        let tcx = self.tcx;

        // And now, for every mentioned method in an impl, add the markers on
        // the corresponding trait method also to the impl method.
        let def_info = known_def_ids
            .iter()
            .map(|id| (*id, def_info_for_item(*id, tcx)))
            .collect();

        let type_info = self.collect_type_info();
        type_info_sanity_check(&controllers, &type_info);
        ProgramDescription {
            type_info,
            instruction_info: self.collect_instruction_info(&controllers),
            controllers,
            def_info,
        }
    }

    /// Create an [`InstructionInfo`] record for each [`GlobalLocation`]
    /// mentioned in the controllers.
    fn collect_instruction_info(
        &self,
        controllers: &HashMap<Endpoint, SPDG>,
    ) -> HashMap<GlobalLocation, InstructionKind> {
        let all_instructions = controllers
            .values()
            .flat_map(|v| {
                v.graph
                    .node_weights()
                    .flat_map(|n| n.at.iter())
                    .chain(v.graph.edge_weights().flat_map(|e| e.at.iter()))
            })
            .collect::<HashSet<_>>();
        all_instructions
            .into_iter()
            .map(|i| {
                let body = self.tcx.body_for_def_id(i.function).unwrap();

                let info = match i.location {
                    RichLocation::End => InstructionKind::Return,
                    RichLocation::Start => InstructionKind::Start,
                    RichLocation::Location(loc) => {
                        let kind = match body.body.stmt_at(loc) {
                            crate::Either::Right(term) => {
                                if let Ok((id, ..)) = term.as_fn_and_args(self.tcx) {
                                    InstructionKind::FunctionCall(FunctionCallInfo {
                                        id,
                                        is_inlined: id.is_local(),
                                    })
                                } else {
                                    InstructionKind::Terminator
                                }
                            }
                            crate::Either::Left(_) => InstructionKind::Statement,
                        };

                        kind
                    }
                };
                (i, info)
            })
            .collect()
    }

    /// Create a [`TypeDescription`] record for each marked type that as
    /// mentioned in the PDG.
    fn collect_type_info(&self) -> TypeInfoMap {
        self.marker_ctx
            .all_annotations()
            .filter(|(id, _)| def_kind_for_item(*id, self.tcx).is_type())
            .into_grouping_map()
            .fold_with(
                |id, _| TypeDescription {
                    rendering: format!("{id:?}"),
                    otypes: vec![],
                    markers: vec![],
                },
                |mut desc, _, ann| {
                    match ann {
                        Either::Right(MarkerAnnotation { refinement, marker })
                        | Either::Left(Annotation::Marker(MarkerAnnotation {
                            refinement,
                            marker,
                        })) => {
                            assert!(refinement.on_self());
                            desc.markers.push(*marker)
                        }
                        Either::Left(Annotation::OType(id)) => desc.otypes.push(*id),
                        _ => panic!("Unexpected type of annotation {ann:?}"),
                    }
                    desc
                },
            )
    }
}

fn src_loc_for_span(span: Span, tcx: TyCtxt) -> SrcCodeSpan {
    let (source_file, start_line, start_col, end_line, end_col) =
        tcx.sess.source_map().span_to_location_info(span);
    let file_path = source_file
        .expect("could not find source file")
        .name
        .display(FileNameDisplayPreference::Local)
        .to_string();
    let abs_file_path = if !file_path.starts_with('/') {
        std::env::current_dir()
            .expect("failed to obtain current working directory")
            .join(&file_path)
    } else {
        std::path::PathBuf::from(&file_path)
    };
    let src_info = SourceFileInfo {
        file_path,
        abs_file_path,
    };
    SrcCodeSpan {
        source_file: src_info.intern(),
        start_line,
        start_col,
        end_line,
        end_col,
    }
}

fn default_index() -> <SPDGImpl as GraphBase>::NodeId {
    <SPDGImpl as GraphBase>::NodeId::end()
}

/// Structure responsible for converting one [`DepGraph`] into an [`SPDG`].
///
/// Intended usage is to call [`Self::new_with_flowistry`] to initialize, then
/// [`Self::make_spdg`] to convert.
struct GraphConverter<'tcx, 'a, C> {
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
    types: HashMap<Node, Types>,
    /// Mapping from old node indices to new node indices. Use
    /// [`Self::register_node`] to insert and [`Self::new_node_for`] to query.
    index_map: Box<[Node]>,
    /// The converted graph we are creating
    spdg: SPDGImpl,
}

impl<'a, 'tcx, C: Extend<DefId>> GraphConverter<'tcx, 'a, C> {
    /// Initialize a new converter by creating an initial PDG using flowistry.
    fn new_with_flowistry(
        generator: &'a SPDGGenerator<'tcx>,
        known_def_ids: &'a mut C,
        target: FnToAnalyze,
    ) -> Result<Self> {
        let local_def_id = target.def_id.expect_local();
        let dep_graph = Rc::new(Self::create_flowistry_graph(generator, local_def_id)?);

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

    /// Try to discern if this node is a special [`NodeKind`]. Also returns if
    /// the location corresponds to a function call for an external function and
    /// any marker annotations on this node.
    fn determine_node_kind(&mut self, weight: &DepNode<'tcx>) -> (NodeKind, Vec<Identifier>) {
        let leaf_loc = weight.at.leaf();

        let body = &self.tcx().body_for_def_id(leaf_loc.function).unwrap().body;

        match leaf_loc.location {
            RichLocation::Start
                if matches!(body.local_kind(weight.place.local), mir::LocalKind::Arg) =>
            {
                let function_id = leaf_loc.function.to_def_id();
                let arg_num = weight.place.local.as_u32() - 1;
                self.known_def_ids.extend(Some(function_id));

                let (annotations, parent) = self.annotations_for_function(function_id, |ann| {
                    ann.refinement.on_argument().contains(arg_num).unwrap()
                });

                self.known_def_ids.extend(parent);
                (NodeKind::FormalParameter(arg_num as u8), annotations)
            }
            RichLocation::End if weight.place.local == mir::RETURN_PLACE => {
                let function_id = leaf_loc.function.to_def_id();
                self.known_def_ids.extend(Some(function_id));
                let (annotations, parent) =
                    self.annotations_for_function(function_id, |ann| ann.refinement.on_return());
                self.known_def_ids.extend(parent);
                (NodeKind::FormalReturn, annotations)
            }
            RichLocation::Location(loc) => {
                let stmt_at_loc = body.stmt_at(loc);
                let matches_place = |place| weight.place.simple_overlaps(place).contains_other();
                if let crate::Either::Right(
                    term @ mir::Terminator {
                        kind:
                            mir::TerminatorKind::Call {
                                args, destination, ..
                            },
                        ..
                    },
                ) = stmt_at_loc
                {
                    let indices: TinyBitSet = args
                        .iter()
                        .enumerate()
                        .filter_map(|(i, op)| matches_place(op.place()?).then_some(i as u32))
                        .collect::<TinyBitSet>();
                    let (fun, ..) = term.as_fn_and_args(self.tcx()).unwrap();
                    self.known_def_ids.extend(Some(fun));
                    let kind = if !indices.is_empty() {
                        NodeKind::ActualParameter(indices)
                    } else if matches_place(*destination) {
                        NodeKind::ActualReturn
                    } else {
                        NodeKind::Unspecified
                    };
                    // TODO implement matching the unspecified node type. OR we
                    // could make sure that there are no unspecified nodes here
                    let annotations = match kind {
                        NodeKind::ActualReturn => {
                            self.annotations_for_function(fun, |ann| ann.refinement.on_return())
                                .0
                        }
                        NodeKind::ActualParameter(index) => {
                            self.annotations_for_function(fun, |ann| {
                                !ann.refinement.on_argument().intersection(index).is_empty()
                            })
                            .0
                        }
                        NodeKind::Unspecified => vec![],
                        _ => unreachable!(),
                    };
                    (kind, annotations)
                } else {
                    // TODO attach annotations if the return value is a marked type
                    (NodeKind::Unspecified, vec![])
                }
            }
            _ => (NodeKind::Unspecified, vec![]),
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

        // So actually we're going to check the base place only, because
        // Flowistry sometimes tracks subplaces instead.
        let place = if self.entrypoint_is_async() {
            let (first, tail) = rest.split_first().unwrap();
            // The body of a top-level `async` function binds a closure to the
            // return place `_0`. Here we expect are looking at the statement
            // that does this binding.
            assert!(self.expect_stmt_at(*first).is_left());
            rest = tail;

            assert_eq!(place.local.as_u32(), 1);
            assert!(place.projection.len() >= 1);
            // in the case of async we'll keep the first projection
            mir::Place {
                local: place.local,
                projection: self.tcx().mk_place_elems(&place.projection[..1]),
            }
        } else {
            place.local.into()
        };
        let resolution = rest.iter().fold(
            FnResolution::Partial(self.local_def_id.to_def_id()),
            |resolution, caller| {
                let terminator = match self.expect_stmt_at(*caller) {
                    Either::Right(t) => t,
                    Either::Left(stmt) => unreachable!("{stmt:?}\nat {caller} in {}", at),
                };
                let term = match resolution {
                    FnResolution::Final(instance) => {
                        Cow::Owned(instance.subst_mir_and_normalize_erasing_regions(
                            tcx,
                            tcx.param_env(resolution.def_id()),
                            ty::EarlyBinder::bind(tcx.erase_regions(terminator.clone())),
                        ))
                    }
                    FnResolution::Partial(_) => Cow::Borrowed(terminator),
                };
                let (instance, ..) = term.as_instance_and_args(tcx).unwrap();
                instance
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
    fn annotations_for_function(
        &self,
        function: DefId,
        mut filter: impl FnMut(&MarkerAnnotation) -> bool,
    ) -> (Vec<Identifier>, Option<DefId>) {
        let parent = get_parent(self.tcx(), function);
        let annotations = self
            .marker_ctx()
            .combined_markers(function)
            .chain(
                parent
                    .into_iter()
                    .flat_map(|parent| self.marker_ctx().combined_markers(parent)),
            )
            .filter(|ann| filter(ann))
            .map(|ann| ann.marker)
            .collect::<Vec<_>>();
        (annotations, parent)
    }

    /// Check if this node is of a marked type and register that type.
    fn handle_node_types(&mut self, i: Node, weight: &DepNode<'tcx>, kind: NodeKind) {
        let is_controller_argument = kind.is_formal_parameter()
            && matches!(self.try_as_root(weight.at), Some(l) if l.location == RichLocation::Start);

        if kind.is_actual_return() {
            assert!(weight.place.projection.is_empty());
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
                .0
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
        let params = flowistry::pdg::PdgParams::new(tcx, local_def_id).with_call_change_callback(
            move |info| {
                let changes = CallChanges::default();

                if is_non_default_trait_method(tcx, info.callee.def_id()).is_some() {
                    tcx.sess.span_warn(
                        tcx.def_span(info.callee.def_id()),
                        "Skipping analysis of unresolvable trait method.",
                    );
                    changes.with_skip(Skip)
                } else if judge.should_inline(info.callee) {
                    changes
                } else {
                    changes.with_skip(Skip)
                }
            },
        );
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

        Ok(flowistry::pdg::compute_pdg(params))
    }

    /// Consume the generator and compile the [`SPDG`].
    fn make_spdg(mut self) -> SPDG {
        let markers = self.make_spdg_impl();
        let arguments = self.determine_arguments();
        let return_ = self.determine_return();
        SPDG {
            graph: self.spdg,
            id: self.local_def_id,
            name: Identifier::new(self.target.name()),
            arguments,
            markers,
            return_,
            type_assigns: self.types,
        }
    }

    /// This initializes the fields `spdg` and `index_map` and should be called first
    fn make_spdg_impl(&mut self) -> HashMap<Node, Vec<Identifier>> {
        use petgraph::prelude::*;
        let g_ref = self.dep_graph.clone();
        let input = &g_ref.graph;
        let tcx = self.tcx();
        let mut markers: HashMap<NodeIndex, Vec<Identifier>> = HashMap::new();

        for (i, weight) in input.node_references() {
            let (kind, node_markers) = self.determine_node_kind(weight);
            let at = weight.at.leaf();
            let body = &tcx.body_for_def_id(at.function).unwrap().body;

            let stmt_span = match at.location {
                RichLocation::End | RichLocation::Start => {
                    let def = &body.local_decls[weight.place.local];
                    def.source_info.span
                }
                RichLocation::Location(loc) => {
                    let expanded_span = match body.stmt_at(loc) {
                        crate::Either::Right(term) => term.source_info.span,
                        crate::Either::Left(stmt) => stmt.source_info.span,
                    };
                    tcx.sess.source_map().stmt_span(expanded_span, body.span)
                }
            };
            let node_span = body.local_decls[weight.place.local].source_info.span;
            // If the span from introducing a local variable is more precise
            // than the one from the statement we use that.
            let rustc_span = if stmt_span.contains(node_span) {
                node_span
            } else {
                stmt_span
            };
            let new_idx = self.register_node(
                i,
                NodeInfo {
                    at: weight.at,
                    description: format!("{:?}", weight.place),
                    kind,
                    span: src_loc_for_span(rustc_span, tcx),
                },
            );

            if !node_markers.is_empty() {
                markers.entry(new_idx).or_default().extend(node_markers);
            }

            self.handle_node_types(new_idx, weight, kind);
        }

        for e in input.edge_references() {
            self.spdg.add_edge(
                self.new_node_for(e.source()),
                self.new_node_for(e.target()),
                EdgeInfo {
                    at: e.weight().at,
                    kind: match e.weight().kind {
                        DepEdgeKind::Control => EdgeKind::Control,
                        DepEdgeKind::Data => EdgeKind::Data,
                    },
                },
            );
        }

        markers
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
    fn determine_return(&self) -> Option<Node> {
        // In async functions
        let mut return_candidates = self
            .spdg
            .node_references()
            .filter(|n| {
                let weight = n.weight();
                let at = weight.at;
                weight.kind.is_formal_return()
                    && matches!(self.try_as_root(at), Some(l) if l.location == RichLocation::End)
            })
            .map(|n| n.id())
            .collect::<Vec<_>>();
        if return_candidates.len() != 1 {
            warn!("Found too many candidates for the return: {return_candidates:?}.");
        }
        return_candidates.pop()
    }

    /// Determine the set if nodes corresponding to the inputs to the
    /// entrypoint. The order is guaranteed to be the same as the source-level
    /// function declaration.
    fn determine_arguments(&self) -> Vec<Node> {
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

/// Checks the invariant that [`SPDGGenerator::collect_type_info`] should
/// produce a map that is a superset of the types found in all the `types` maps
/// on [`SPDG`].
///
/// Additionally this also inserts missing types into the map *only* for
/// generators created by async functions.
fn type_info_sanity_check(controllers: &ControllerMap, types: &TypeInfoMap) {
    controllers
        .values()
        .flat_map(|spdg| spdg.type_assigns.values())
        .flat_map(|types| &types.0)
        .for_each(|t| {
            assert!(
                types.contains_key(t),
                "Invariant broken: Type {t:?} is not present in type map"
            );
        })
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

fn def_kind_for_item(id: DefId, tcx: TyCtxt) -> DefKind {
    match tcx.def_kind(id) {
        def::DefKind::Closure => DefKind::Closure,
        def::DefKind::Generator => DefKind::Generator,
        kind if kind.is_fn_like() => DefKind::Fn,
        def::DefKind::Struct
        | def::DefKind::AssocTy
        | def::DefKind::OpaqueTy
        | def::DefKind::TyAlias { .. }
        | def::DefKind::Enum => DefKind::Type,
        kind => unreachable!("{} ({:?})", tcx.def_path_debug_str(id), kind),
    }
}

fn def_info_for_item(id: DefId, tcx: TyCtxt) -> DefInfo {
    let name = crate::utils::identifier_for_item(tcx, id);
    let kind = def_kind_for_item(id, tcx);
    let def_path = tcx.def_path(id);
    let path = std::iter::once(Identifier::new(tcx.crate_name(def_path.krate)))
        .chain(def_path.data.iter().filter_map(|segment| {
            use hir::definitions::DefPathDataName::*;
            match segment.data.name() {
                Named(sym) => Some(Identifier::new(sym)),
                Anon { .. } => None,
            }
        }))
        .collect();
    DefInfo {
        name,
        path,
        kind,
        src_info: src_loc_for_span(tcx.def_span(id), tcx),
    }
}

/// A higher order function that increases the logging level if the `target`
/// matches the one selected with the `debug` flag on the command line (and
/// reset it afterward).
fn with_reset_level_if_target<R, F: FnOnce() -> R>(opts: &crate::Args, target: Symbol, f: F) -> R {
    if matches!(opts.direct_debug(), LogLevelConfig::Targeted(s) if target.as_str() == s) {
        with_temporary_logging_level(opts.verbosity(), f)
    } else {
        f()
    }
}
