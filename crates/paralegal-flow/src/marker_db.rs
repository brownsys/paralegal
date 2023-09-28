//! Central repository for information about markers (and annotations).
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
use rustc_utils::cache::{Cache, CopyCache};

use std::rc::Rc;

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

impl<'tcx> MarkerCtx<'tcx> {
    /// Constructs a new marker database.
    ///
    /// This also loads any external annotations, as specified in the `args`.
    pub fn new(tcx: TyCtxt<'tcx>, args: &'static Args) -> Self {
        Self(Rc::new(MarkerDatabase::init(tcx, args)))
    }

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
            .get(def_id, |_| self.retrieve_local_annotations_for(def_id))
            .as_ref()
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
            .items()
            .into_iter()
            .filter_map(|(k, v)| Some((k, (v.as_ref()?.as_slice()))))
            .collect()
    }

    /// Direct access to the loaded database of external markers.
    #[inline]
    pub fn external_annotations(&self) -> &ExternalMarkers {
        &self.db().external_annotations
    }

    /// Are there markers reachable from this (function)?
    ///
    /// Returns true if the item itself carries a marker *or* if one of the
    /// functions called in its body are marked.
    ///
    /// XXX Does not take into account reachable type markers
    pub fn marker_is_reachable(&self, def_id: DefId) -> bool {
        self.is_marked(def_id) || self.has_transitive_reachable_markers(def_id)
    }

    /// Queries the transitive marker cache.
    fn has_transitive_reachable_markers(&self, def_id: DefId) -> bool {
        self.db()
            .marker_reachable_cache
            .get_maybe_recursive(def_id, |_| self.compute_marker_reachable(def_id))
            .unwrap_or(false)
    }

    /// If the transitive marker cache did not contain the answer, this is what
    /// computes it.
    fn compute_marker_reachable(&self, def_id: DefId) -> bool {
        let body = match self.tcx().body_for_def_id(def_id) {
            Ok(body) => body,
            Err(e) => {
                warn!(
                    "Marker reachability for {} was asked but is unknown ({})",
                    self.tcx().def_path_debug_str(def_id),
                    e
                );
                return false;
            }
        }
        .simplified_body();
        body.basic_blocks
            .iter()
            .any(|bbdat| self.terminator_carries_marker(&body.local_decls, bbdat.terminator()))
    }

    /// Does this terminator carry a marker?
    fn terminator_carries_marker(
        &self,
        local_decls: &mir::LocalDecls,
        terminator: &mir::Terminator<'tcx>,
    ) -> bool {
        if let Ok((defid, _args, _)) = terminator.as_fn_and_args(self.tcx()) {
            debug!(
                "Checking function {} for markers",
                self.tcx().def_path_debug_str(defid)
            );
            if self.marker_is_reachable(defid) {
                return true;
            }
            if let ty::TyKind::Alias(ty::AliasKind::Opaque, alias) =
                    local_decls[mir::RETURN_PLACE].ty.kind()
                && let ty::TyKind::Generator(closure_fn, _, _) = self.tcx().type_of(alias.def_id).skip_binder().kind() {
                return self.marker_is_reachable(
                    *closure_fn
                );
            }
        }
        false
    }

    /// Retrieve and parse the local annotations for this item.
    fn retrieve_local_annotations_for(&self, def_id: LocalDefId) -> LocalAnnotations {
        let tcx = self.tcx();
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
        if sink_matches.is_empty() {
            return None;
        }

        Some(Box::new(sink_matches))
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

    /// All markers placed on this function, directly or through the type.
    pub fn all_function_markers<'a>(
        &'a self,
        function: FnResolution<'tcx>,
    ) -> impl Iterator<Item = (&'a MarkerAnnotation, Option<(ty::Ty<'tcx>, DefId)>)> {
        self.combined_markers(function.def_id())
            .zip(std::iter::repeat(None))
            .chain(
                (self.0.config.local_function_type_marking() || !function.def_id().is_local())
                    .then(|| {
                        self.all_type_markers(function.sig(self.tcx()).skip_binder().output())
                            .map(|(marker, typeinfo)| (marker, Some(typeinfo)))
                    })
                    .into_iter()
                    .flatten(),
            )
    }
}

/// We expect most local items won't have annotations. This structure is much
/// smaller (8 bytes) than without the `Box` (24 Bytes).
#[allow(clippy::box_collection)]
type LocalAnnotations = Option<Box<Vec<Annotation>>>;

/// The structure inside of [`MarkerCtx`].
struct MarkerDatabase<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Cache for parsed local annotations. They are created with
    /// [`MarkerCtx::retrieve_local_annotations_for`].
    local_annotations: Cache<LocalDefId, LocalAnnotations>,
    external_annotations: ExternalMarkers,
    /// Cache whether markers are reachable transitively.
    marker_reachable_cache: CopyCache<DefId, bool>,
    /// Configuration options
    config: &'static MarkerControl,
}

impl<'tcx> MarkerDatabase<'tcx> {
    /// Construct a new database, loading external markers.
    fn init(tcx: TyCtxt<'tcx>, args: &'static Args) -> Self {
        Self {
            tcx,
            local_annotations: Cache::default(),
            external_annotations: resolve_external_markers(args, tcx),
            marker_reachable_cache: Default::default(),
            config: args.marker_control(),
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
                    .unwrap_or_else(|err| panic!("Could not resolve {path}: {err:?}"));
                let did = match res {
                    Res::Def(_, did) => Some(did),
                    other if opts.relaxed() => {
                        warn!("{path} did not resolve to an item ({other:?})");
                        None
                    }
                    other => panic!("{path} did not resolve to an item ({other:?})"),
                }?;
                Some((did, marker.clone()))
            })
            .collect();
        assert_eq!(new_map.len(), from_toml.len());
        new_map
    } else {
        HashMap::new()
    }
}
