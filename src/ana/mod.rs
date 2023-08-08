//! Data-and control flow analyzer and inliner.
//!
//!

use std::borrow::Cow;

use crate::{
    dbg, desc::*, ir::*, rust::*, utils::*, Either, HashMap, HashSet, LogLevelConfig, Symbol,
};

use hir::def_id::DefId;
use mir::Location;

use rustc_utils::mir::borrowck_facts;

use super::discover::{CallSiteAnnotations, CollectingVisitor, FnToAnalyze};

pub mod algebra;
pub mod df;
pub mod inline;
pub mod non_transitive_aliases;

pub type SerializableInlinedGraph<L> =
    petgraph::graphmap::GraphMap<regal::SimpleLocation<L>, inline::Edge, petgraph::Directed>;

impl<'tcx> CollectingVisitor<'tcx> {
    /// Driver function. Performs the data collection via visit, then calls
    /// [`Self::analyze`] to construct the Forge friendly description of all
    /// endpoints.
    pub fn run(mut self) -> std::io::Result<ProgramDescription> {
        let tcx = self.tcx;
        tcx.hir().visit_all_item_likes_in_crate(&mut self);
        //println!("{:?}\n{:?}\n{:?}", self.marked_sinks, self.marked_sources, self.functions_to_analyze);
        self.analyze()
    }

    /// Perform the analysis for one `#[dfpp::analyze]` annotated function and
    /// return the representation suitable for emitting into Forge.
    fn handle_target<'g>(
        &self,
        //_hash_verifications: &mut HashVerifications,
        call_site_annotations: &mut CallSiteAnnotations,
        target: FnToAnalyze,
        gli: GLI<'g>,
        inliner: &inline::Inliner<'tcx, 'g>,
    ) -> std::io::Result<(Endpoint, Ctrl)> {
        let mut flows = Ctrl::default();
        let local_def_id = self.tcx.hir().body_owner_def_id(target.body_id);
        fn register_call_site(
            map: &mut CallSiteAnnotations,
            did: DefId,
            ann: Option<&[Annotation]>,
        ) {
            map.entry(did)
                .and_modify(|e| {
                    e.extend(ann.iter().flat_map(|a| a.iter()).cloned());
                })
                .or_insert_with(|| ann.iter().flat_map(|a| a.iter()).cloned().collect());
        }
        let tcx = self.tcx;
        let controller_body_with_facts =
            borrowck_facts::get_simplified_body_with_borrowck_facts(tcx, local_def_id);

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
                                .basic_blocks
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
                let subtypes = self
                    .marker_ctx
                    .all_type_markers(ty)
                    .map(|t| Identifier::new(t.0.marker))
                    .collect::<HashSet<_>>();
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
            let (_, (instance, _, _)) = match inner_body
                .stmt_at_better_err(inner_location)
                .right()
                .ok_or("not a terminator".to_owned())
                .and_then(|t| {
                    Ok((
                        t,
                        t.as_instance_and_args(tcx).map_err(|e| format!("{e:?}"))?,
                    ))
                }) {
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
            let defid = instance.def_id();
            let call_site = CallSite::new(loc, defid, tcx);
            // Propagate annotations on the function object to the call site
            register_call_site(
                call_site_annotations,
                defid,
                defid
                    .as_local()
                    .map_or(None, |ldid| self.marker_ctx.local_annotations(ldid)),
            );

            let interesting_output_types: HashSet<_> = self
                .marker_ctx
                .all_function_markers(instance)
                .filter_map(|(_, t)| Some(identifier_for_item(self.tcx, t?.1)))
                .collect();
            if !interesting_output_types.is_empty() {
                flows.types.0.insert(
                    DataSource::FunctionCall(call_site.clone()),
                    interesting_output_types,
                );
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

        let inliner = inline::Inliner::new(
            self.tcx,
            gli,
            self.marker_ctx.clone(),
            self.opts.anactrl(),
            self.opts.dbg(),
        );

        let mut call_site_annotations: CallSiteAnnotations = HashMap::new();
        let result = //crate::sah::HashVerifications::with(|hash_verifications| {
            targets
                .drain(..)
                .map(|desc| {
                    let target_name = desc.name();
                    with_reset_level_if_target(self.opts, target_name, || {
                        self.handle_target(
                            //hash_verifications,
                            &mut call_site_annotations,
                            desc,
                            gli,
                            &inliner,
                        )
                    })
                })
                .collect::<std::io::Result<HashMap<Endpoint, Ctrl>>>()
                .map(|controllers| ProgramDescription {
                    controllers,
                    annotations: self.marker_ctx.local_annotations_found()
                        .into_iter()
                        .map(|(k, v)| (k.to_def_id(), v.to_vec()))
                        .chain(self.marker_ctx.external_annotations().iter().map(|(did, anns)| {
                            (
                                *did,
                                anns.iter().cloned().map(Annotation::Label).collect(),
                            )
                        }))
                        .map(|(did, anns)| {
                            let def_kind = tcx.def_kind(did);
                            let obj_type = if def_kind.is_fn_like() {
                                ObjectType::Function(
                                    tcx.fn_sig(did).skip_binder().skip_binder().inputs().len(),
                                )
                            } else {
                                // XXX add an actual match here
                                ObjectType::Type
                            };
                            (identifier_for_item(tcx, did), (anns, obj_type))
                        })
                        .collect(),
                });
        //});
        info!(
            "Total number of analyzed functions {}",
            inliner.cache_size()
        );
        result
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
