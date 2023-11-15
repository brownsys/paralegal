//! Central repository for information about markers (and annotations).
//!
//! The database ([`MarkerDatabase`]) is initialized with
//! ([`init`](`MarkerDatabase::init`)) and populated with local markers by
//! [`CollectingVisitor`](crate::discover::CollectingVisitor) by calls to
//! ([`retrieve_local_annotations_for`](MarkerDatabase::retrieve_local_annotations_for)).
//! Then it's transformed into a read-only [`MarkerCtx`] via [`From::from`]. The
//! [`MarkerCtx`] is a cheap pointer to the database and responsible for
//! answering queries about markers as the main analysis runs.
//!
//! All interactions happen through the central database object: [`MarkerCtx`].

use crate::{
    args::{Args, MarkerControl},
    consts,
    desc::{Annotation, MarkerAnnotation},
    mir, ty,
    utils::{
        AsFnAndArgs, FnResolution, GenericArgExt, IntoDefId, IntoHirId, MetaItemMatch, TyCtxtExt,
        TyExt,
    },
    DefId, HashMap, LocalDefId, TyCtxt,
};
use rustc_utils::cache::CopyCache;

use std::{borrow::Cow, rc::Rc};

type ExternalMarkers = HashMap<DefId, Vec<MarkerAnnotation>>;

/// The marker context is a database which can be queried as to whether
/// functions or types carry markers, whether markers are reachable in bodies,
/// etc.
///
/// The idea is that this struct provides basic information about the presence
/// of markers and takes care of memoizing and caching such information
/// efficiently but it does not interpret what this information means.
/// Interpretation is done by [`crate::ana::inline::InlineJudge`].
///
/// This is a smart-pointer wrapper around the actual payload ([`MarkerDatabase`]).
#[derive(Clone)]
pub struct MarkerCtx<'tcx>(Rc<MarkerDatabase<'tcx>>);

impl<'tcx> From<MarkerDatabase<'tcx>> for MarkerCtx<'tcx> {
    fn from(value: MarkerDatabase<'tcx>) -> Self {
        Self(Rc::new(value))
    }
}

impl<'tcx> MarkerCtx<'tcx> {
    #[inline]
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.0.tcx
    }

    #[inline]
    fn db(&self) -> &MarkerDatabase<'tcx> {
        &self.0
    }

    /// Retrieves the local annotations for this item. If no such annotations
    /// are present an empty slice is returned.
    ///
    /// Query is cached.
    pub fn local_annotations(&self, def_id: LocalDefId) -> &[Annotation] {
        self.db()
            .local_annotations
            .get(&def_id)
            .map_or(&[], |o| o.as_slice())
    }

    /// Retrieves any external markers on this item. If there are not such
    /// markers an empty slice is returned.
    ///
    /// THe external marker database is populated at construction.
    pub fn external_markers<D: IntoDefId>(&self, did: D) -> &[MarkerAnnotation] {
        self.db()
            .external_annotations
            .get(&did.into_def_id(self.tcx()))
            .map_or(&[], |v| v.as_slice())
    }

    /// All markers reachable for this item (local and external).
    ///
    /// Queries are cached/precomputed so calling this repeatedly is cheap.
    pub fn combined_markers(&self, def_id: DefId) -> impl Iterator<Item = &MarkerAnnotation> {
        def_id
            .as_local()
            .map(|ldid| self.local_annotations(ldid))
            .into_iter()
            .flat_map(|anns| anns.iter().flat_map(Annotation::as_marker))
            .chain(self.external_markers(def_id).iter())
    }

    /// Are there any external markers on this item?
    pub fn is_externally_marked<D: IntoDefId>(&self, did: D) -> bool {
        !self.external_markers(did).is_empty()
    }

    /// Are there any local markers on this item?
    pub fn is_locally_marked(&self, def_id: LocalDefId) -> bool {
        self.local_annotations(def_id)
            .iter()
            .any(Annotation::is_marker)
    }

    #[cfg_attr(feature = "profiling", flamer::flame)]
    /// Are there any markers (local or external) on this item?
    ///
    /// This is in contrast to [`Self::marker_is_reachable`] which also reports
    /// if markers are reachable from the body of this function (if it is one).
    pub fn is_marked<D: IntoDefId + Copy>(&self, did: D) -> bool {
        matches!(did.into_def_id(self.tcx()).as_local(), Some(ldid) if self.is_locally_marked(ldid))
            || self.is_externally_marked(did)
    }

    /// Return a complete set of local annotations that were discovered.
    ///
    /// Crucially this is a "readout" from the marker cache, which means only
    /// items reachable from the `paralegal_flow::analyze` will end up in this collection.
    pub fn local_annotations_found(&self) -> Vec<(LocalDefId, &[Annotation])> {
        self.db()
            .local_annotations
            .iter()
            .map(|(k, v)| (*k, (v.as_slice())))
            .collect()
    }

    /// Direct access to the loaded database of external markers.
    #[inline]
    pub fn external_annotations(&self) -> &ExternalMarkers {
        &self.db().external_annotations
    }

    #[cfg_attr(feature = "profiling", flamer::flame)]
    /// Are there markers reachable from this (function)?
    ///
    /// Returns true if the item itself carries a marker *or* if one of the
    /// functions called in its body are marked.
    ///
    /// XXX Does not take into account reachable type markers
    pub fn marker_is_reachable(&self, res: FnResolution<'tcx>) -> bool {
        self.is_marked(res.def_id()) || self.has_transitive_reachable_markers(res)
    }

    /// Queries the transitive marker cache.
    pub fn has_transitive_reachable_markers(&self, res: FnResolution<'tcx>) -> bool {
        self.db()
            .marker_reachable_cache
            .get_maybe_recursive(res, |_| self.compute_marker_reachable(res))
            .unwrap_or(false)
    }

    /// If the transitive marker cache did not contain the answer, this is what
    /// computes it.
    fn compute_marker_reachable(&self, res: FnResolution<'tcx>) -> bool {
        let Some(body) = self.tcx().body_for_def_id_default_policy(res.def_id()) else {
            return false;
        };
        let body = body.simplified_body();
        body.basic_blocks.iter().any(|bbdat| {
            let term = match res {
                FnResolution::Final(inst) => {
                    Cow::Owned(inst.subst_mir_and_normalize_erasing_regions(
                        self.tcx(),
                        ty::ParamEnv::reveal_all(),
                        bbdat.terminator().clone(),
                    ))
                }
                FnResolution::Partial(_) => Cow::Borrowed(bbdat.terminator()),
            };
            self.terminator_carries_marker(&body.local_decls, term.as_ref())
        })
    }

    /// Does this terminator carry a marker?
    fn terminator_carries_marker(
        &self,
        local_decls: &mir::LocalDecls,
        terminator: &mir::Terminator<'tcx>,
    ) -> bool {
        if let Ok((res, _args, _)) = terminator.as_instance_and_args(self.tcx()) {
            debug!(
                "Checking function {} for markers",
                self.tcx().def_path_debug_str(res.def_id())
            );
            if self.marker_is_reachable(res) {
                return true;
            }
            if let ty::TyKind::Alias(ty::AliasKind::Opaque, alias) =
                    local_decls[mir::RETURN_PLACE].ty.kind()
                && let ty::TyKind::Generator(closure_fn, substs, _) = self.tcx().type_of(alias.def_id).skip_binder().kind() {
                return self.marker_is_reachable(
                    FnResolution::Final(ty::Instance::expect_resolve(self.tcx(), ty::ParamEnv::reveal_all(), *closure_fn, substs))
                );
            }
        }
        false
    }

    /// All the markers applied to this type and its subtypes.
    ///
    /// Returns `(ann, (ty, did))` tuples which are the marker annotation `ann`,
    /// the specific type `ty` that it was applied to and the `did` [`Defid`] of
    /// that type that was used to look up the annotations.
    pub fn all_type_markers<'a>(
        &'a self,
        ty: ty::Ty<'tcx>,
    ) -> impl Iterator<Item = (&'a MarkerAnnotation, (ty::Ty<'tcx>, DefId))> {
        ty.walk().filter_map(|g| g.as_type()).flat_map(move |typ| {
            typ.defid().into_iter().flat_map(move |did| {
                self.combined_markers(did)
                    .zip(std::iter::repeat((typ, did)))
            })
        })
    }

    /// All markers placed on this function, directly or through the type plus
    /// the type that was marked (if any).
    pub fn all_function_markers<'a>(
        &'a self,
        function: FnResolution<'tcx>,
    ) -> impl Iterator<Item = (&'a MarkerAnnotation, Option<(ty::Ty<'tcx>, DefId)>)> {
        // Markers not coming from types, hence the "None"
        let direct_markers = self
            .combined_markers(function.def_id())
            .zip(std::iter::repeat(None));
        let get_type_markers = || {
            let sig = function.sig(self.tcx()).ok()?;
            let output = sig.output();
            // XXX I'm not entirely sure this is how we should do
            // this. For now I'm calling this "okay" because it's
            // basically the old behavior
            if output.is_closure() || output.is_generator() {
                return None;
            }
            Some(
                self.all_type_markers(output)
                    .map(|(marker, typeinfo)| (marker, Some(typeinfo))),
            )
        };

        let include_type_markers =
            self.0.config.local_function_type_marking() || !function.def_id().is_local();
        direct_markers.chain(
            if include_type_markers {
                get_type_markers()
            } else {
                None
            }
            .into_iter()
            .flatten(),
        )
    }
}
/// The structure inside of [`MarkerCtx`].
pub struct MarkerDatabase<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Cache for parsed local annotations. They are created with
    /// [`MarkerCtx::retrieve_local_annotations_for`].
    local_annotations: HashMap<LocalDefId, Vec<Annotation>>,
    external_annotations: ExternalMarkers,
    /// Cache whether markers are reachable transitively.
    marker_reachable_cache: CopyCache<FnResolution<'tcx>, bool>,
    /// Configuration options
    config: &'static MarkerControl,
}

impl<'tcx> MarkerDatabase<'tcx> {
    /// Construct a new database, loading external markers.
    pub fn init(tcx: TyCtxt<'tcx>, args: &'static Args) -> Self {
        Self {
            tcx,
            local_annotations: HashMap::default(),
            external_annotations: resolve_external_markers(args, tcx),
            marker_reachable_cache: Default::default(),
            config: args.marker_control(),
        }
    }

    /// Retrieve and parse the local annotations for this item.
    pub fn retrieve_local_annotations_for(&mut self, def_id: LocalDefId) {
        let tcx = self.tcx;
        let hir = tcx.hir();
        let id = def_id.force_into_hir_id(tcx);
        let mut sink_matches = vec![];
        for a in hir.attrs(id) {
            if let Some(i) = a.match_get_ref(&consts::MARKER_MARKER) {
                sink_matches.push(Annotation::Marker(crate::ann_parse::ann_match_fn(i)));
            } else if let Some(i) = a.match_get_ref(&consts::LABEL_MARKER) {
                warn!("The `paralegal_flow::label` annotation is deprecated, use `paralegal_flow::marker` instead");
                sink_matches.push(Annotation::Marker(crate::ann_parse::ann_match_fn(i)))
            } else if let Some(i) = a.match_get_ref(&consts::OTYPE_MARKER) {
                sink_matches.extend(
                    crate::ann_parse::otype_ann_match(i, tcx)
                        .into_iter()
                        .map(Annotation::OType),
                );
            } else if let Some(i) = a.match_get_ref(&consts::EXCEPTION_MARKER) {
                sink_matches.push(Annotation::Exception(crate::ann_parse::match_exception(i)));
            }
        }
        if !sink_matches.is_empty() {
            assert!(self
                .local_annotations
                .insert(def_id, sink_matches)
                .is_none());
        }
    }
}

type RawExternalMarkers = HashMap<String, Vec<crate::desc::MarkerAnnotation>>;

/// Given the TOML of external annotations we have parsed, resolve the paths
/// (keys of the map) to [`DefId`]s.
fn resolve_external_markers(opts: &Args, tcx: TyCtxt) -> ExternalMarkers {
    if let Some(annotation_file) = opts.modelctrl().external_annotations() {
        let from_toml: RawExternalMarkers = toml::from_str(
            &std::fs::read_to_string(annotation_file).unwrap_or_else(|_| {
                panic!(
                    "Could not open file {}/{}",
                    std::env::current_dir().unwrap().display(),
                    annotation_file.display()
                )
            }),
        )
        .unwrap();
        use crate::utils::resolve::{def_path_res, Res};
        let new_map: ExternalMarkers = from_toml
            .iter()
            .filter_map(|(path, marker)| {
                let segment_vec = path.split("::").collect::<Vec<_>>();
                let res = def_path_res(tcx, &segment_vec)
                    .map_err(|err| tcx.sess.err(format!("Could not resolve {path}: {err:?}")))
                    .ok()?;
                let did = match res {
                    Res::Def(_, did) => Some(did),
                    other => {
                        let msg = format!("{path} did not resolve to an item ({other:?})");
                        if opts.relaxed() {
                            tcx.sess.warn(msg);
                        } else {
                            tcx.sess.err(msg);
                        }
                        None
                    }
                }?;
                Some((did, marker.clone()))
            })
            .collect();
        new_map
    } else {
        HashMap::new()
    }
}
