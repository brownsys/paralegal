//! Data-and control flow analyzer and inliner.
//!
//!

use std::borrow::Cow;

use crate::{
    dbg, desc::*, ir::*, rust::*, sah::HashVerifications, utils::*, Either, HashMap, HashSet,
    LogLevelConfig, Symbol,
};

use hir::def_id::DefId;
use mir::Location;
use rustc_hir::def_id::LocalDefId;

use flowistry::mir::borrowck_facts;

use super::discover::{CallSiteAnnotations, CollectingVisitor, FnToAnalyze};

pub mod algebra;
pub mod df;
mod inline;
pub mod non_transitive_aliases;

impl<'tcx> CollectingVisitor<'tcx> {
    /// Driver function. Performs the data collection via visit, then calls
    /// [`Self::analyze`] to construct the Forge friendly description of all
    /// endpoints.
    pub fn run(mut self) -> std::io::Result<ProgramDescription> {
        let tcx = self.tcx;
        tcx.hir().deep_visit_all_item_likes(&mut self);
        //println!("{:?}\n{:?}\n{:?}", self.marked_sinks, self.marked_sources, self.functions_to_analyze);
        self.analyze()
    }

    /// Perform the analysis for one `#[dfpp::analyze]` annotated function and
    /// return the representation suitable for emitting into Forge.
    fn handle_target<'g>(
        &self,
        _hash_verifications: &mut HashVerifications,
        call_site_annotations: &mut CallSiteAnnotations,
        interesting_fn_defs: &HashMap<DefId, (Vec<Annotation>, usize)>,
        target: FnToAnalyze,
        gli: GLI<'g>,
        inliner: &inline::Inliner<'tcx, 'g, '_>,
    ) -> std::io::Result<(Endpoint, Ctrl)> {
        let mut flows = Ctrl::default();
        let local_def_id = self.tcx.hir().body_owner_def_id(target.body_id);
        fn register_call_site<'tcx>(
            tcx: TyCtxt<'tcx>,
            map: &mut CallSiteAnnotations,
            did: DefId,
            ann: Option<&[Annotation]>,
        ) {
            map.entry(did)
                .and_modify(|e| {
                    e.0.extend(ann.iter().flat_map(|a| a.iter()).cloned());
                })
                .or_insert_with(|| {
                    (
                        ann.iter().flat_map(|a| a.iter()).cloned().collect(),
                        tcx.fn_sig(did).skip_binder().inputs().len(),
                    )
                });
        }
        let tcx = self.tcx;
        let controller_body_with_facts =
            borrowck_facts::get_body_with_borrowck_facts(tcx, local_def_id);

        if self.opts.dbg().dump_ctrl_mir() {
            mir::graphviz::write_mir_fn_graphviz(
                tcx,
                controller_body_with_facts.simplified_body(),
                false,
                &mut outfile_pls(format!("{}.mir.gv", target.name())).unwrap(),
            )
            .unwrap()
        }

        debug!("Handling target {}", target.name());

        let flow = {
            let w = 6;
            let i = inliner.get_inlined_graph(target.body_id).unwrap();
            info!("Graph statistics for {}\n  {:<w$} graph nodes\n  {:<w$} graph edges\n  {:<w$} inlined functions\n  {:<w$} max call stack depth", target.name(), i.vertex_count(), i.edge_count(), i.inlined_functions_count(), i.max_call_stack_depth());
            inliner.to_call_only_flow(i, |a| {
                gli.globalize_location(
                    Location {
                        block: mir::BasicBlock::from_usize(
                            controller_body_with_facts
                                .simplified_body()
                                .basic_blocks()
                                .len(),
                        ),
                        statement_index: a as usize + 1,
                    },
                    target.body_id,
                )
            })
        };

        // Register annotations on argument types for this controller.
        let controller_body = &controller_body_with_facts.simplified_body();
        {
            let types = controller_body.args_iter().map(|l| {
                let ty = controller_body.local_decls[l].ty;
                let subtypes = self.annotated_subtypes(ty);
                (DataSource::Argument(l.as_usize() - 1), subtypes)
            });
            flows.add_types(types);
        }

        if self.opts.dbg().dump_serialized_non_transitive_graph() {
            dbg::write_non_transitive_graph_and_body(
                tcx,
                &flow,
                outfile_pls(format!("{}.ntgb.json", target.name())).unwrap(),
            );
        }

        if self.opts.dbg().dump_call_only_flow() {
            outfile_pls(format!("{}.call-only-flow.gv", target.name()))
                .and_then(|mut file| dbg::call_only_flow_dot::dump(tcx, &flow, &mut file))
                .unwrap_or_else(|err| {
                    error!("Could not write transitive graph dump, reason: {err}")
                })
        }

        let check_realness = |l: mir::Location| l.is_real(controller_body);

        for (loc, deps) in flow.location_dependencies.iter() {
            // It's important to look at the innermost location. It's easy to
            // use `location()` and `function()` on a global location instead
            // but that is the outermost call site, not the location for the actual call.
            let GlobalLocationS {
                location: inner_location,
                function: inner_body_id,
            } = loc.innermost();
            // We need to make sure to fetch the body again here, because we
            // might be looking at an inlined location, so the body we operate
            // on bight not be the `body` we fetched before.
            let inner_body_with_facts = tcx.body_for_body_id(inner_body_id);
            let inner_body = &inner_body_with_facts.simplified_body();
            if !inner_location.is_real(inner_body) {
                assert!(loc.is_at_root());
                // These can only be (controller) arguments and they cannot have
                // dependencies (and thus not receive any data)
                continue;
            }
            let (terminator, (defid, _, _)) = match inner_body
                .stmt_at_better_err(inner_location)
                .right()
                .ok_or("not a terminator".to_owned())
                .and_then(|t| Ok((t, t.as_fn_and_args().map_err(|e| format!("{e:?}"))?)))
            {
                Ok(term) => term,
                Err(err) => {
                    // We expect to always encounter function calls at this
                    // stage so this could be a hard error, but I made it a
                    // warning because that makes it easier to debug (because
                    // you can see other important down-the-line output that
                    // gives moire information to this error).
                    warn!(
                        "Odd location in graph creation '{}' for {:?}",
                        err,
                        inner_body.stmt_at(inner_location)
                    );
                    continue;
                }
            };
            let call_site = CallSite::new(loc, defid, tcx);
            // Propagate annotations on the function object to the call site
            register_call_site(
                tcx,
                call_site_annotations,
                defid,
                interesting_fn_defs.get(&defid).map(|a| a.0.as_slice()),
            );

            let stmt_anns = self.statement_anns_by_loc(defid, terminator);
            let bound_sig = tcx.fn_sig(defid);
            let interesting_output_types: HashSet<_> =
                self.annotated_subtypes(bound_sig.skip_binder().output());
            if !interesting_output_types.is_empty() {
                flows.types.0.insert(
                    DataSource::FunctionCall(call_site.clone()),
                    interesting_output_types,
                );
            }
            if let Some(_anns) = stmt_anns {
                // This is currently commented out because hash verification is
                // buggy
                unimplemented!();
                // for ann in anns.iter().filter_map(Annotation::as_exception_annotation) {
                //     //hash_verifications.handle(ann, tcx, terminator, &body, loc, matrix);
                // }
                // TODO this is attaching to functions instead of call
                // sites. Once we start actually tracking call sites
                // this needs to be adjusted
                // register_call_site(tcx, call_site_annotations, defid, Some(anns));
            }

            // Add ctrl flows to callsite.
            for dep in deps.ctrl_deps.iter() {
                flows.add_ctrl_flow(
                    Cow::Owned(dep.as_data_source(tcx, check_realness)),
                    call_site.clone(),
                )
            }

            debug!("Adding dependencies from {loc}");

            for (arg_slot, arg_deps) in deps.input_deps.iter().enumerate() {
                debug!("  on argument {arg_slot}");
                // This will be the target of any flow we register
                let to = if loc.is_at_root()
                    && matches!(
                        inner_body.stmt_at_better_err(loc.outermost_location()),
                        Either::Right(mir::Terminator {
                            kind: mir::TerminatorKind::Return,
                            ..
                        })
                    ) {
                    DataSink::Return
                } else {
                    DataSink::Argument {
                        function: call_site.clone(),
                        arg_slot,
                    }
                };
                for dep in arg_deps.iter() {
                    debug!("    to {dep}");
                    flows.add_data_flow(
                        Cow::Owned(dep.as_data_source(tcx, check_realness)),
                        to.clone(),
                    );
                }
            }
        }
        for dep in flow.return_dependencies.iter() {
            flows.add_data_flow(
                Cow::Owned(dep.as_data_source(tcx, check_realness)),
                DataSink::Return,
            );
        }
        Ok((identifier_for_item(tcx, target.body_id), flows))
    }

    /// Main analysis driver. Essentially just calls [`Self::handle_target`]
    /// once for every function in `self.functions_to_analyze` after doing some
    /// other setup necessary for the flow graph creation.
    ///
    /// Should only be called after the visit.
    fn analyze(mut self) -> std::io::Result<ProgramDescription> {
        let arena = rustc_arena::TypedArena::default();
        let interner = GlobalLocationInterner::new(&arena);
        let gli = GLI::new(&interner);
        let tcx = self.tcx;
        let mut targets = std::mem::take(&mut self.functions_to_analyze);
        let interesting_fn_defs = self
            .marked_objects
            .as_ref()
            .borrow()
            .iter()
            .filter_map(|(s, v)| match v.1 {
                ObjectType::Function(i) => {
                    Some((tcx.hir().local_def_id(*s).to_def_id(), (v.0.clone(), i)))
                }
                _ => None,
            })
            .collect::<HashMap<_, _>>();

        if let LogLevelConfig::Targeted(s) = &*self.opts.debug() {
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

        let recurse_selector = SkipAnnotatedFunctionSelector {
            marked_objects: self.marked_objects.clone(),
            tcx,
        };

        let inliner = inline::Inliner::new(
            self.tcx,
            gli,
            &recurse_selector,
            self.opts.anactrl(),
            self.opts.dbg(),
        );

        let mut call_site_annotations: CallSiteAnnotations = HashMap::new();
        let result = crate::sah::HashVerifications::with(|hash_verifications| {
            targets
                .drain(..)
                .map(|desc| {
                    let target_name = desc.name();
                    with_reset_level_if_target(self.opts, target_name, || {
                        self.handle_target(
                            hash_verifications,
                            &mut call_site_annotations,
                            &interesting_fn_defs,
                            desc,
                            gli,
                            &inliner,
                        )
                    })
                })
                .collect::<std::io::Result<HashMap<Endpoint, Ctrl>>>()
                .map(|controllers| ProgramDescription {
                    controllers,
                    annotations: call_site_annotations
                        .into_iter()
                        .map(|(k, v)| {
                            (
                                identifier_for_item(tcx, k),
                                (v.0, ObjectType::Function(v.1)),
                            )
                        })
                        .chain(
                            self.marked_objects
                                .as_ref()
                                .borrow()
                                .iter()
                                .filter(|kv| kv.1 .1 == ObjectType::Type)
                                .map(|(k, v)| (identifier_for_item(tcx, *k), v.clone())),
                        )
                        .chain(self.external_annotations.iter().map(|(did, (anns, typ))| {
                            (
                                identifier_for_item(tcx, did),
                                (
                                    anns.iter().cloned().map(Annotation::Label).collect(),
                                    typ.clone(),
                                ),
                            )
                        }))
                        .collect(),
                })
        });
        info!(
            "Total number of analyzed functions {}",
            inliner.cache_size()
        );
        result
    }

    fn annotated_subtypes(&self, ty: ty::Ty) -> HashSet<TypeDescriptor> {
        ty.walk()
            .filter_map(|ty| {
                ty.as_type()
                    .and_then(TyExt::defid)
                    //.and_then(DefId::as_local)
                    .and_then(|def| {
                        let maybe_item_name = self.tcx.opt_item_name(def);
                        if maybe_item_name.is_none() {
                            info!("Could not find item name for type {ty:?}");
                        }
                        let item_name = identifier_for_item(self.tcx, def);
                        if def.as_local().map_or(false, |ldef| {
                            self.marked_objects
                                .as_ref()
                                .borrow()
                                .contains_key(&self.tcx.hir().local_def_id_to_hir_id(ldef))
                        }) || self.external_annotations.contains_key(&def)
                        {
                            Some(item_name)
                        } else {
                            None
                        }
                    })
            })
            .collect()
    }

    /// Extract all types mentioned in this type for which we have annotations.
    /// XXX: This selector is somewhat problematic. For one it matches via
    /// source locations, rather than id, and for another we're using `find`
    /// here, which would discard additional matching annotations.
    fn statement_anns_by_loc(&self, p: DefId, t: &mir::Terminator<'tcx>) -> Option<&[Annotation]> {
        self.marked_stmts
            .iter()
            .find(|(_, (_, s, f))| p == *f && s.contains(t.source_info.span))
            .map(|t| t.1 .0 .0.as_slice())
    }
}

/// A higher order function that increases the logging level if the `target`
/// matches the one selected with the `debug` flag on the command line (and
/// reset it afterward).
fn with_reset_level_if_target<R, F: FnOnce() -> R>(opts: &crate::Args, target: Symbol, f: F) -> R {
    if matches!(&*opts.debug(), LogLevelConfig::Targeted(s) if target.as_str() == s) {
        with_temporary_logging_level(log::LevelFilter::Debug, f)
    } else {
        f()
    }
}

/// The only implementation of [`InlineSelector`] currently in use. This skips
/// inlining for all `LocalDefId` values that are found in the map of
/// `self.marked_objects` i.e. all those functions that have annotations.
#[derive(Clone)]
struct SkipAnnotatedFunctionSelector<'tcx> {
    marked_objects: crate::discover::MarkedObjects,
    tcx: TyCtxt<'tcx>,
}
impl<'tcx> inline::Oracle<'tcx> for SkipAnnotatedFunctionSelector<'tcx> {
    fn should_inline(&self, did: LocalDefId) -> bool {
        self.marked_objects
            .as_ref()
            .borrow()
            .get(&self.tcx.hir().local_def_id_to_hir_id(did))
            .map_or(true, |anns| anns.0.is_empty())
    }

    fn is_semantically_meaningful(&self, did: DefId) -> bool {
        matches!(did.as_local(), Some(l) if !self.should_inline(l))
    }
}
