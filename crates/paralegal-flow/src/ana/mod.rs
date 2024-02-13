//! Data-and control flow analyzer and inliner.
//!
//! Analysis starts with the construction of [`SPDGGenerator`] from a
//! [`CollectingVisitor`](crate::discover::CollectingVisitor) and then calling
//! [`analyze`](SPDGGenerator::analyze).

use crate::{
    desc::*, rust::*, utils::*, DefId, HashMap, HashSet, LogLevelConfig, MarkerCtx, Symbol,
};
use std::borrow::Cow;
use std::rc::Rc;

use anyhow::{anyhow, Result};
use either::Either;
use flowistry::pdg::graph::{DepEdgeKind, DepGraph, DepNode};
use flowistry::pdg::CallChanges;
use flowistry::pdg::SkipCall::Skip;
use paralegal_spdg::{utils::display_list, Node};
use petgraph::visit::{GraphBase, IntoNodeReferences, NodeIndexable, NodeRef};

use super::discover::FnToAnalyze;

pub mod inline;

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
        if let LogLevelConfig::Targeted(s) = self.opts.debug() {
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
        let result = targets
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
            .map(|controllers| self.make_program_description(controllers, &known_def_ids));
        result
    }

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
        ProgramDescription {
            type_info: self.collect_type_info(&controllers),
            instruction_info: self.collect_instruction_info(&controllers),
            controllers,
            def_info,
        }
    }

    fn collect_instruction_info(
        &self,
        controllers: &HashMap<Endpoint, SPDG>,
    ) -> HashMap<GlobalLocation, InstructionInfo> {
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
                    RichLocation::End => InstructionInfo::Return,
                    RichLocation::Start => InstructionInfo::Start,
                    RichLocation::Location(loc) => match body.body.stmt_at(loc) {
                        crate::Either::Right(term) => {
                            if let Ok((id, ..)) = term.as_fn_and_args(self.tcx) {
                                InstructionInfo::FunctionCall(FunctionCallInfo {
                                    id,
                                    is_inlined: id.is_local(),
                                })
                            } else {
                                InstructionInfo::Terminator
                            }
                        }
                        _ => InstructionInfo::Statement,
                    },
                };
                (i, info)
            })
            .collect()
    }

    fn collect_type_info(
        &self,
        controllers: &HashMap<Endpoint, SPDG>,
    ) -> HashMap<TypeId, TypeDescription> {
        let types = controllers
            .values()
            .flat_map(|v| v.types.values())
            .flat_map(|t| &t.0)
            .copied()
            .collect::<HashSet<_>>();
        types
            .into_iter()
            .map(|t| {
                (
                    t,
                    TypeDescription {
                        rendering: format!("{t:?}"),
                        otypes: if let Some(l) = t.as_local() {
                            self.marker_ctx
                                .local_annotations(l)
                                .iter()
                                .filter_map(Annotation::as_otype)
                                .collect()
                        } else {
                            vec![]
                        },
                        markers: self
                            .marker_ctx
                            .combined_markers(t)
                            .map(|t| t.marker)
                            .collect(),
                    },
                )
            })
            .collect()
    }
}

struct GraphConverter<'tcx, 'a, C> {
    generator: &'a SPDGGenerator<'tcx>,
    known_def_ids: &'a mut C,
    target: FnToAnalyze,
    dep_graph: Rc<DepGraph<'tcx>>,
    /// Same as the ID stored in self.target, but as a local def id
    local_def_id: LocalDefId,
    types: HashMap<Node, Types>,
    markers: HashMap<Node, Vec<Identifier>>,
}

impl<'a, 'tcx, C: Extend<DefId>> GraphConverter<'tcx, 'a, C> {
    fn new_with_flowistry(
        generator: &'a SPDGGenerator<'tcx>,
        known_def_ids: &'a mut C,
        target: FnToAnalyze,
    ) -> Result<Self> {
        let local_def_id = target.def_id.expect_local();
        let dep_graph = Rc::new(Self::create_flowistry_graph(generator, local_def_id)?);

        if generator.opts.dbg().dump_flowistry_pdg() {
            dep_graph.generate_graphviz(format!("{}.flowistry-pdg.pdf", target.name))?
        }

        Ok(Self {
            generator,
            known_def_ids,
            target,
            dep_graph,
            local_def_id,
            types: Default::default(),
            markers: Default::default(),
        })
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.generator.tcx
    }

    fn marker_ctx(&self) -> &MarkerCtx<'tcx> {
        &self.generator.marker_ctx
    }

    fn entrypoint_is_async(&self) -> bool {
        self.tcx().asyncness(self.local_def_id).is_async()
    }

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

    fn determine_node_kind(&mut self, i: Node, weight: &DepNode<'tcx>) -> (NodeKind, bool) {
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
                if !annotations.is_empty() {
                    self.markers
                        .entry(i)
                        .or_insert_with(Default::default)
                        .extend(annotations);
                }
                (NodeKind::FormalParameter(arg_num as u8), false)
            }
            RichLocation::End if weight.place.local == mir::RETURN_PLACE => {
                let function_id = leaf_loc.function.to_def_id();
                self.known_def_ids.extend(Some(function_id));
                let (annotations, parent) =
                    self.annotations_for_function(function_id, |ann| ann.refinement.on_return());
                self.known_def_ids.extend(parent);
                if !annotations.is_empty() {
                    self.markers
                        .entry(i)
                        .or_insert_with(Default::default)
                        .extend(annotations);
                }
                (NodeKind::FormalReturn, false)
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
                    let is_external = !fun.is_local();
                    let kind = if !indices.is_empty() {
                        NodeKind::ActualParameter(indices)
                    } else if matches_place(*destination) {
                        NodeKind::ActualReturn
                    } else {
                        NodeKind::Unspecified
                    };
                    (kind, is_external)
                } else {
                    (NodeKind::Unspecified, false)
                }
            }
            _ => (NodeKind::Unspecified, false),
        }
    }

    fn determine_place_type(&self, weight: &DepNode<'tcx>) -> mir::tcx::PlaceTy<'tcx> {
        let tcx = self.tcx();
        let locations = weight.at.iter_from_root().collect::<Vec<_>>();
        let (last, mut rest) = locations.split_last().unwrap();

        if self.entrypoint_is_async() {
            let (first, tail) = rest.split_first().unwrap();
            // The body of a top-level `async` function binds a closure to the
            // return place `_0`. Here we expect are looking at the statement
            // that does this binding.
            assert!(self.expect_stmt_at(*first).is_left());
            rest = tail;
        }
        let resolution = rest.iter().fold(
            FnResolution::Partial(self.local_def_id.to_def_id()),
            |resolution, caller| {
                let crate::Either::Right(terminator) = self.expect_stmt_at(*caller) else {
                    unreachable!()
                };
                let term = match resolution {
                    FnResolution::Final(instance) => {
                        Cow::Owned(instance.subst_mir_and_normalize_erasing_regions(
                            tcx,
                            tcx.param_env(resolution.def_id()),
                            ty::EarlyBinder::bind(terminator.clone()),
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
        let raw_ty = weight.place.ty(&body.body, tcx);
        match resolution {
            FnResolution::Partial(_) => raw_ty,
            FnResolution::Final(instance) => instance.subst_mir_and_normalize_erasing_regions(
                tcx,
                ty::ParamEnv::reveal_all(),
                ty::EarlyBinder::bind(tcx.erase_regions(raw_ty)),
            ),
        }
    }

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

    fn handle_node_types(
        &mut self,
        i: Node,
        weight: &DepNode<'tcx>,
        is_external_call_source: bool,
    ) {
        let place_ty = self.determine_place_type(weight);

        let type_markers = self.type_is_marked(place_ty, is_external_call_source);
        self.known_def_ids.extend(type_markers.iter().copied());
        if !type_markers.is_empty() {
            self.types
                .entry(i)
                .or_insert_with(Default::default)
                .0
                .extend(type_markers)
        }
    }

    fn create_flowistry_graph(
        generator: &SPDGGenerator<'tcx>,
        local_def_id: LocalDefId,
    ) -> Result<DepGraph<'tcx>> {
        let tcx = generator.tcx;
        let opts = generator.opts;
        let marker_context = generator.marker_ctx.clone();
        let params = flowistry::pdg::PdgParams::new(tcx, local_def_id);
        let params = if opts.anactrl().use_recursive_analysis() {
            params.with_call_change_callback(move |info| {
                let changes = CallChanges::default();

                if marker_context.is_marked(info.callee.def_id()) {
                    changes.with_skip(Skip)
                } else {
                    changes
                }
            })
        } else {
            params.with_call_change_callback(|_| CallChanges::default().with_skip(Skip))
        };

        if opts.dbg().dump_mir() {
            let mut file =
                std::fs::File::create(format!("{}.mir", body_name_pls(tcx, local_def_id)))?;
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

    fn make_spdg(mut self) -> SPDG {
        let graph = self.make_spdg_impl();
        let arguments = self.determine_arguments(&graph);
        let return_ = self.determine_return(&graph);
        SPDG {
            graph,
            name: Identifier::new(self.target.name()),
            arguments,
            markers: self.markers,
            return_,
            types: self.types,
        }
    }

    fn make_spdg_impl(&mut self) -> SPDGImpl {
        use petgraph::prelude::*;
        let g_ref = self.dep_graph.clone();
        let input = &g_ref.graph;
        let mut g = SPDGImpl::new();

        let default_index = <SPDGImpl as GraphBase>::NodeId::end();
        let mut index_map = vec![default_index; input.node_bound()];

        for (i, weight) in input.node_references() {
            let (kind, is_external_call_source) = self.determine_node_kind(i, weight);
            debug_assert!(index_map[i.index()] == default_index);
            index_map[i.index()] = g.add_node(NodeInfo {
                at: weight.at,
                description: format!("{:?}", weight.place),
                kind,
            });

            self.handle_node_types(i, weight, is_external_call_source);
        }

        for e in input.edge_references() {
            g.add_edge(
                index_map[e.source().index()],
                index_map[e.target().index()],
                EdgeInfo {
                    at: e.weight().at,
                    kind: match e.weight().kind {
                        DepEdgeKind::Control => EdgeKind::Control,
                        DepEdgeKind::Data => EdgeKind::Data,
                    },
                },
            );
        }

        g
    }

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

    fn determine_return(&self, graph: &SPDGImpl) -> Option<Node> {
        let mut return_candidates = graph
            .node_references()
            .filter(|n| {
                let weight = n.weight();
                let at = weight.at;
                let is_candidate = weight.kind.is_formal_return()
                    && at.is_at_root()
                    && at.leaf().location == RichLocation::End;
                assert!(!is_candidate || self.local_def_id == at.leaf().function);
                is_candidate
            })
            .map(|n| n.id())
            .peekable();
        let picked = return_candidates.next()?;
        assert!(
            return_candidates.peek().is_none(),
            "Found too many candidates for the return. {} was picked but also \
            found {}",
            DisplayNode::pretty(picked, graph),
            display_list(
                return_candidates
                    .map(|i| DisplayNode::pretty(i, graph))
                    .collect::<Vec<_>>()
            ),
        );
        Some(picked)
    }

    fn determine_arguments(&self, graph: &SPDGImpl) -> Vec<Node> {
        graph
            .node_references()
            .filter(|n| {
                let at = n.weight().at;
                let is_candidate = at.is_at_root() && at.leaf().location == RichLocation::Start;
                assert!(!is_candidate || self.local_def_id == at.leaf().function);
                is_candidate
            })
            .map(|n| n.id())
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

fn def_info_for_item(id: DefId, tcx: TyCtxt) -> DefInfo {
    use hir::def;
    let name = crate::utils::identifier_for_item(tcx, id);
    let kind = match tcx.def_kind(id) {
        def::DefKind::Closure => DefKind::Closure,
        def::DefKind::Generator => DefKind::Generator,
        kind if kind.is_fn_like() => DefKind::Fn,
        def::DefKind::Struct
        | def::DefKind::AssocTy
        | def::DefKind::OpaqueTy
        | def::DefKind::TyAlias { .. }
        | def::DefKind::Enum => DefKind::Type,
        _ => unreachable!("{}", tcx.def_path_debug_str(id)),
    };
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
    DefInfo { name, path, kind }
}

/// A higher order function that increases the logging level if the `target`
/// matches the one selected with the `debug` flag on the command line (and
/// reset it afterward).
fn with_reset_level_if_target<R, F: FnOnce() -> R>(opts: &crate::Args, target: Symbol, f: F) -> R {
    if matches!(opts.debug(), LogLevelConfig::Targeted(s) if target.as_str() == s) {
        with_temporary_logging_level(log::LevelFilter::Debug, f)
    } else {
        f()
    }
}
