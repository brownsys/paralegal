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
    ann::{Annotation, MarkerAnnotation},
    args::{Args, MarkerControl},
    ast::Attribute,
    consts,
    hir::def::DefKind,
    mir, ty,
    utils::{
        resolve::expect_resolve_string_to_def_id, AsFnAndArgs, FnResolution, FnResolutionExt,
        IntoDefId, IntoHirId, MetaItemMatch, TyCtxtExt, TyExt,
    },
    DefId, Either, HashMap, HashSet, LocalDefId, TyCtxt,
};
use flowistry_pdg_construction::determine_async;
use paralegal_spdg::Identifier;
use rustc_utils::cache::Cache;

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
            .get(&self.defid_rewrite(def_id.to_def_id()).expect_local())
            .map_or(&[], |o| o.as_slice())
    }

    /// Retrieves any external markers on this item. If there are not such
    /// markers an empty slice is returned.
    ///
    /// THe external marker database is populated at construction.
    pub fn external_markers<D: IntoDefId>(&self, did: D) -> &[MarkerAnnotation] {
        self.db()
            .external_annotations
            .get(&self.defid_rewrite(did.into_def_id(self.tcx())))
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

    /// For async handling. If this id corresponds to an async closure we try to
    /// resolve its parent item which the markers would actually be placed on.
    fn defid_rewrite(&self, def_id: DefId) -> DefId {
        let def_kind = self.tcx().def_kind(def_id);
        if matches!(def_kind, DefKind::Generator) {
            if let Some(parent) = self.tcx().opt_parent(def_id) {
                if matches!(self.tcx().def_kind(parent), DefKind::AssocFn | DefKind::Fn)
                    && self.tcx().asyncness(parent).is_async()
                {
                    return parent;
                }
            };
        }
        def_id
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
            .iter()
            .map(|(k, v)| (*k, (v.as_slice())))
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
    pub fn marker_is_reachable(&self, res: FnResolution<'tcx>) -> bool {
        self.is_marked(res.def_id()) || self.has_transitive_reachable_markers(res)
    }

    /// Queries the transitive marker cache.
    pub fn has_transitive_reachable_markers(&self, res: FnResolution<'tcx>) -> bool {
        !self.get_reachable_markers(res).is_empty()
    }

    pub fn get_reachable_markers(&self, res: FnResolution<'tcx>) -> &[Identifier] {
        self.db()
            .reachable_markers
            .get_maybe_recursive(res, |_| self.compute_reachable_markers(res))
            .map_or(&[], Box::as_ref)
    }

    fn get_reachable_and_self_markers(
        &self,
        res: FnResolution<'tcx>,
    ) -> impl Iterator<Item = Identifier> + '_ {
        if res.def_id().is_local() {
            let mut direct_markers = self
                .combined_markers(res.def_id())
                .map(|m| m.marker)
                .peekable();
            let non_direct = direct_markers
                .peek()
                .is_none()
                .then(|| self.get_reachable_markers(res));

            Either::Right(direct_markers.chain(non_direct.into_iter().flatten().copied()))
        } else {
            Either::Left(
                self.all_function_markers(res)
                    .map(|m| m.0.marker)
                    .collect::<Vec<_>>(),
            )
        }
        .into_iter()
    }

    /// If the transitive marker cache did not contain the answer, this is what
    /// computes it.
    fn compute_reachable_markers(&self, res: FnResolution<'tcx>) -> Box<[Identifier]> {
        let Some(local) = res.def_id().as_local() else {
            return Box::new([]);
        };
        if self.is_marked(res.def_id()) {
            return Box::new([]);
        }
        let Some(body) = self.tcx().body_for_def_id_default_policy(local) else {
            return Box::new([]);
        };
        let mono_body = res.try_monomorphize(self.tcx(), ty::ParamEnv::reveal_all(), &body.body);
        if let Some((async_fn, _)) = determine_async(self.tcx(), local, &mono_body) {
            return self.get_reachable_markers(async_fn).into();
        }
        let body = &body.body;
        body.basic_blocks
            .iter()
            .flat_map(|bbdat| {
                self.terminator_reachable_markers(&body.local_decls, bbdat.terminator())
            })
            .collect::<HashSet<_>>()
            .into_iter()
            .collect()
    }

    /// Does this terminator carry a marker?
    fn terminator_reachable_markers(
        &self,
        local_decls: &mir::LocalDecls,
        terminator: &mir::Terminator<'tcx>,
    ) -> impl Iterator<Item = Identifier> + '_ {
        if let Ok((res, _args, _)) = terminator.as_instance_and_args(self.tcx()) {
            debug!(
                "Checking function {} for markers",
                self.tcx().def_path_debug_str(res.def_id())
            );
            let transitive_reachable = self.get_reachable_and_self_markers(res);
            let others = if let ty::TyKind::Alias(ty::AliasKind::Opaque, alias) =
                    local_decls[mir::RETURN_PLACE].ty.kind()
                && let ty::TyKind::Generator(closure_fn, substs, _) = self.tcx().type_of(alias.def_id).skip_binder().kind() {
                Either::Left(self.get_reachable_and_self_markers(
                    FnResolution::Final(ty::Instance::expect_resolve(self.tcx(), ty::ParamEnv::reveal_all(), *closure_fn, substs))
                ))
            } else {
                Either::Right(std::iter::empty())
            };
            Either::Right(transitive_reachable.chain(others))
        } else {
            Either::Left(std::iter::empty())
        }.into_iter()
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

    pub fn type_markers<'a>(&'a self, key: ty::Ty<'tcx>) -> &'a TypeMarkers<'tcx> {
        self.0
            .type_markers
            .get(key, |key| {
                use ty::*;
                let tcx = self.tcx();
                let mut markers = Vec::new();
                match key.kind() {
                    Bool
                    | Char
                    | Int(_)
                    | Uint(_)
                    | Float(_)
                    | Foreign(_)
                    | Str
                    | FnDef { .. }
                    | FnPtr { .. }
                    | Closure { .. }
                    | Generator { .. }
                    | GeneratorWitness { .. }
                    | GeneratorWitnessMIR { .. }
                    | Never
                    | Bound { .. }
                    | Error(_) => (),
                    Adt(def, generics) => markers.extend(self.type_markers_for_adt(def, &generics)),
                    Tuple(tys) => markers.extend(tys.iter().enumerate().flat_map(|(idx, ty)| {
                        let project = Box::new([mir::PlaceElem::Field(idx.into(), ty)]);
                        self.submarkers_projected(project, ty)
                    })),
                    Alias(_, inner) => return self.type_markers(inner.to_ty(tcx)).into(),
                    // We can't track indices so we simply overtaint to the entire array
                    Array(inner, _) | Slice(inner) => markers.extend(
                        self.type_markers(*inner)
                            .iter()
                            .map(|(_, marker)| (ty::List::empty(), *marker)),
                    ),
                    RawPtr(ty::TypeAndMut { ty, .. }) | Ref(_, ty, _) => markers
                        .extend(self.submarkers_projected(Box::new([mir::PlaceElem::Deref]), *ty)),
                    Param(_) | Dynamic { .. } => self
                        .tcx()
                        .sess
                        .warn(format!("Cannot determine markers for type {key:?}")),
                    Placeholder(_) | Infer(_) => self
                        .tcx()
                        .sess
                        .fatal(format!("Did not expect this type here {key:?}")),
                }
                markers.as_slice().into()
            })
            .as_ref()
    }

    fn submarkers_projected<'a>(
        &'a self,
        projection: Box<[mir::PlaceElem<'tcx>]>,
        t: ty::Ty<'tcx>,
    ) -> impl Iterator<Item = TypeMarkerElem<'tcx>> + 'a {
        self.type_markers(t)
            .iter()
            .map(move |(inner_projection, marker)| {
                (
                    self.tcx().mk_place_elems_from_iter(
                        projection.iter().copied().chain(inner_projection.iter()),
                    ),
                    *marker,
                )
            })
    }

    fn type_markers_for_adt<'a>(
        &'a self,
        adt: &'a ty::AdtDef<'tcx>,
        generics: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ) -> impl Iterator<Item = TypeMarkerElem<'tcx>> + 'a {
        let tcx = self.tcx();
        adt.variants()
            .iter_enumerated()
            .flat_map(move |(vidx, vdef)| {
                vdef.fields.iter_enumerated().flat_map(move |(fidx, fdef)| {
                    let f_ty = fdef.ty(tcx, generics);
                    let variant_project = adt
                        .is_enum()
                        .then_some(mir::PlaceElem::Downcast(Some(vdef.name), vidx));
                    let outer_projection = variant_project
                        .into_iter()
                        .chain([mir::PlaceElem::Field(fidx, f_ty)])
                        .collect::<Box<_>>();
                    self.submarkers_projected(outer_projection, f_ty)
                })
            })
    }

    pub fn type_has_surface_markers(&self, ty: ty::Ty) -> Option<DefId> {
        let def_id = ty.defid()?;
        self.combined_markers(def_id)
            .next()
            .is_some()
            .then_some(def_id)
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

    /// Iterate over all discovered annotations, whether local or external
    pub fn all_annotations(
        &self,
    ) -> impl Iterator<Item = (DefId, Either<&Annotation, &MarkerAnnotation>)> {
        self.0
            .local_annotations
            .iter()
            .flat_map(|(&id, anns)| {
                anns.iter()
                    .map(move |ann| (id.to_def_id(), Either::Left(ann)))
            })
            .chain(
                self.0
                    .external_annotations
                    .iter()
                    .flat_map(|(&id, anns)| anns.iter().map(move |ann| (id, Either::Right(ann)))),
            )
    }
}

pub type TypeMarkerElem<'tcx> = (&'tcx ty::List<mir::PlaceElem<'tcx>>, Identifier);
pub type TypeMarkers<'tcx> = [TypeMarkerElem<'tcx>];

/// The structure inside of [`MarkerCtx`].
pub struct MarkerDatabase<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Cache for parsed local annotations. They are created with
    /// [`MarkerCtx::retrieve_local_annotations_for`].
    local_annotations: HashMap<LocalDefId, Vec<Annotation>>,
    external_annotations: ExternalMarkers,
    /// Cache whether markers are reachable transitively.
    reachable_markers: Cache<FnResolution<'tcx>, Box<[Identifier]>>,
    /// Configuration options
    config: &'static MarkerControl,
    type_markers: Cache<ty::Ty<'tcx>, Box<TypeMarkers<'tcx>>>,
}

impl<'tcx> MarkerDatabase<'tcx> {
    /// Construct a new database, loading external markers.
    pub fn init(tcx: TyCtxt<'tcx>, args: &'static Args) -> Self {
        Self {
            tcx,
            local_annotations: HashMap::default(),
            external_annotations: resolve_external_markers(args, tcx),
            reachable_markers: Default::default(),
            config: args.marker_control(),
            type_markers: Default::default(),
        }
    }

    /// Retrieve and parse the local annotations for this item.
    pub fn retrieve_local_annotations_for(&mut self, def_id: LocalDefId) {
        let tcx = self.tcx;
        let hir = tcx.hir();
        let id = def_id.force_into_hir_id(tcx);
        for a in hir.attrs(id) {
            match try_parse_annotation(tcx, a) {
                Ok(anns) => {
                    let mut anns = anns.peekable();
                    if anns.peek().is_some() {
                        self.local_annotations
                            .entry(def_id)
                            .or_default()
                            .extend(anns)
                    }
                }
                Err(e) => {
                    tcx.sess.span_err(a.span, e);
                }
            }
        }
    }
}

fn try_parse_annotation(
    tcx: TyCtxt,
    a: &Attribute,
) -> Result<impl Iterator<Item = Annotation>, String> {
    use crate::ann::parse::{ann_match_fn, match_exception, otype_ann_match};
    let one = |a| Either::Left(Some(a));
    let ann = if let Some(i) = a.match_get_ref(&consts::MARKER_MARKER) {
        one(Annotation::Marker(ann_match_fn(i)?))
    } else if let Some(i) = a.match_get_ref(&consts::LABEL_MARKER) {
        warn!("The `paralegal_flow::label` annotation is deprecated, use `paralegal_flow::marker` instead");
        one(Annotation::Marker(ann_match_fn(i)?))
    } else if let Some(i) = a.match_get_ref(&consts::OTYPE_MARKER) {
        Either::Right(otype_ann_match(i, tcx)?.into_iter().map(Annotation::OType))
    } else if let Some(i) = a.match_get_ref(&consts::EXCEPTION_MARKER) {
        one(Annotation::Exception(match_exception(i)?))
    } else {
        Either::Left(None)
    };
    Ok(ann.into_iter())
}

type RawExternalMarkers = HashMap<String, Vec<crate::ann::MarkerAnnotation>>;

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
        let new_map: ExternalMarkers = from_toml
            .iter()
            .filter_map(|(path, marker)| {
                Some((
                    expect_resolve_string_to_def_id(tcx, path, opts.relaxed())?,
                    marker.clone(),
                ))
            })
            .collect();
        new_map
    } else {
        HashMap::new()
    }
}
