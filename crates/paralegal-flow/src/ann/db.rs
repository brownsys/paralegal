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
    args::{Args, Stub},
    utils::{
        func_of_term, resolve::expect_resolve_string_to_def_id, FunctionKind, InstanceExt,
        IntoDefId, TyExt,
    },
    Either, HashMap, HashSet,
};
use flowistry::mir::FlowistryInput;
use flowistry_pdg_construction::{
    body_cache::{local_or_remote_paths, BodyCache},
    determine_async,
    encoder::ParalegalDecoder,
    utils::{handle_shims, is_virtual, try_monomorphize, try_resolve_function},
};
use paralegal_spdg::Identifier;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_errors::DiagMessage;
use rustc_hir::def_id::DefId;
use rustc_hir::{def::DefKind, def_id::CrateNum};
use rustc_middle::{
    mir,
    ty::{self, GenericArgsRef, Instance, TyCtxt, TypingEnv},
};
use rustc_serialize::Decodable;

use rustc_span::Span;
use rustc_utils::cache::Cache;

use std::{borrow::Cow, fs::File, io::Read, rc::Rc};

use super::{MarkerMeta, MarkerRefinement, MARKER_META_EXT};

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
    pub fn source_annotations(&self, def_id: DefId) -> &[Annotation] {
        self.db()
            .annotations
            .get(&self.defid_rewrite(def_id))
            .map_or(&[], |b| b)
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
        self.source_annotations(def_id)
            .iter()
            .filter_map(Annotation::as_marker)
            .chain(self.external_markers(def_id).iter())
    }

    /// For async handling. If this id corresponds to an async closure we try to
    /// resolve its parent item which the markers would actually be placed on.
    fn defid_rewrite(&self, def_id: DefId) -> DefId {
        if self.tcx().is_coroutine(def_id) {
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
    pub fn is_locally_marked(&self, def_id: DefId) -> bool {
        self.source_annotations(def_id)
            .iter()
            .any(Annotation::is_marker)
    }

    /// Are there any markers (local or external) on this item?
    ///
    /// This is in contrast to [`Self::marker_is_reachable`] which also reports
    /// if markers are reachable from the body of this function (if it is one).
    pub fn is_marked<D: IntoDefId + Copy>(&self, did: D) -> bool {
        let defid = did.into_def_id(self.tcx());
        self.is_locally_marked(defid) || self.is_externally_marked(defid)
    }

    /// Return a complete set of local annotations that were discovered.
    ///
    /// Crucially this is a "readout" from the marker cache, which means only
    /// items reachable from the `paralegal_flow::analyze` will end up in this collection.
    pub fn source_annotations_found(&self) -> Vec<(DefId, &[Annotation])> {
        self.db()
            .annotations
            .iter()
            .map(|(k, v)| (*k, v.as_slice()))
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
    pub fn marker_is_reachable(&self, res: Instance<'tcx>) -> bool {
        self.is_marked(res.def_id()) || self.has_transitive_reachable_markers(res)
    }

    /// Queries the transitive marker cache.
    pub fn has_transitive_reachable_markers(
        &self,
        res: impl Into<MaybeMonomorphized<'tcx>>,
    ) -> bool {
        !self.get_reachable_markers(res).is_empty()
    }

    pub fn get_reachable_markers(&self, res: impl Into<MaybeMonomorphized<'tcx>>) -> &[Identifier] {
        let res = res.into();
        let def_id = res.def_id();
        if self.is_marked(def_id) {
            trace!("  Is marked");
            return &[];
        }
        if is_virtual(self.tcx(), def_id) {
            trace!("  Is virtual");
            return &[];
        }
        if !self.0.included_crates.contains(&def_id.krate) {
            return &[];
        }
        self.db()
            .reachable_markers
            .get_maybe_recursive(&res, |_| self.compute_reachable_markers(res))
            .map_or(&[], Box::as_ref)
    }

    fn get_reachable_and_self_markers(
        &self,
        res: impl Into<MaybeMonomorphized<'tcx>>,
    ) -> impl Iterator<Item = Identifier> + '_ {
        let res = res.into();
        let mut direct_markers = self
            .combined_markers(res.def_id())
            .map(|m| m.marker)
            .peekable();
        let non_direct = direct_markers
            .peek()
            .is_none()
            .then(|| self.get_reachable_markers(res));

        direct_markers.chain(non_direct.into_iter().flatten().copied())
    }

    /// If the transitive marker cache did not contain the answer, this is what
    /// computes it.
    fn compute_reachable_markers(&self, res: MaybeMonomorphized<'tcx>) -> Box<[Identifier]> {
        trace!("Computing reachable markers for {res:?}");
        let body = self.0.body_cache.get(res.def_id());
        let mono_body = match res {
            MaybeMonomorphized::Monomorphized(res) => Cow::Owned(
                try_monomorphize(
                    res,
                    self.tcx(),
                    TypingEnv::post_analysis(self.tcx(), res.def_id())
                        .with_post_analysis_normalized(self.tcx()),
                    body.body(),
                    self.tcx().def_span(res.def_id()),
                )
                .unwrap(),
            ),
            MaybeMonomorphized::Plain(_) => Cow::Borrowed(body.body()),
        };
        if let Some((async_fn, _, _)) = determine_async(self.tcx(), res.def_id(), &mono_body) {
            return self.get_reachable_markers(async_fn).into();
        }
        let expect_resolve = res.is_monomorphized();
        let variable_markers = mono_body
            .local_decls
            .iter()
            .flat_map(|v| self.deep_type_markers(v.ty))
            .map(|(_, m)| *m);
        mono_body
            .basic_blocks
            .iter()
            .flat_map(|bbdat| {
                self.terminator_reachable_markers(
                    &mono_body.local_decls,
                    bbdat.terminator(),
                    expect_resolve,
                )
            })
            .chain(variable_markers)
            .collect::<HashSet<_>>()
            .into_iter()
            .collect()
    }

    fn span_err(&self, span: Span, msg: impl Into<DiagMessage>) {
        if self.0.config.relaxed() {
            self.tcx().dcx().span_warn(span, msg.into());
        } else {
            self.tcx().dcx().span_err(span, msg.into());
        }
    }

    /// Does this terminator carry a marker?
    fn terminator_reachable_markers(
        &self,
        local_decls: &mir::LocalDecls,
        terminator: &mir::Terminator<'tcx>,
        expect_resolve: bool,
    ) -> impl Iterator<Item = Identifier> + '_ {
        let param_env = TypingEnv::fully_monomorphized();
        let mut v = vec![];
        trace!(
            "  Finding reachable markers for terminator {:?}",
            terminator.kind
        );
        let Some((def_id, gargs)) = func_of_term(self.tcx(), terminator) else {
            return v.into_iter();
        };
        let mut res = if expect_resolve {
            let Some(instance) =
                Instance::try_resolve(self.tcx(), param_env, def_id, gargs).unwrap()
            else {
                self.span_err(
                        terminator.source_info.span,
                        format!("cannot determine reachable markers, failed to resolve {def_id:?} with {gargs:?}")
                    );
                return v.into_iter();
            };
            MaybeMonomorphized::Monomorphized(
                handle_shims(instance, self.tcx(), param_env, terminator.source_info.span)
                    .map_or(instance, |(shimmed, _)| shimmed),
            )
        } else {
            MaybeMonomorphized::Plain(def_id)
        };
        trace!(
            "    Checking function {} for markers",
            self.tcx().def_path_debug_str(res.def_id())
        );

        if let Some(model) = self.has_stub(res.def_id()) {
            if let MaybeMonomorphized::Monomorphized(instance) = &mut res {
                if let Ok(new_instance) = model.resolve_alternate_instance(
                    self.tcx(),
                    *instance,
                    param_env,
                    terminator.source_info.span,
                ) {
                    v.extend(self.get_reachable_and_self_markers(new_instance));
                }
            } else {
                self.span_err(
                    terminator.source_info.span,
                    "Could not apply stub to an partially resolved function",
                );
            };
            return v.into_iter();
        }

        v.extend(self.get_reachable_and_self_markers(res));

        // We have to proceed differently than graph construction,
        // because we are not given the closure function, instead
        // we are provided the id of the function that creates the
        // future. As such we can't just monomorphize and traverse,
        // we have to find the generator first.
        if let ty::TyKind::Alias(ty::AliasTyKind::Opaque, alias) =
            local_decls[mir::RETURN_PLACE].ty.kind()
            && let ty::TyKind::Coroutine(closure_fn, substs) =
                self.tcx().type_of(alias.def_id).skip_binder().kind()
        {
            trace!("    fits opaque type");
            v.extend(
                self.get_reachable_and_self_markers(
                    try_resolve_function(
                        self.tcx(),
                        *closure_fn,
                        TypingEnv::fully_monomorphized(),
                        substs,
                    )
                    .unwrap(),
                ),
            )
        };
        v.into_iter()
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

    pub fn shallow_type_markers<'a>(
        &'a self,
        key: ty::Ty<'tcx>,
    ) -> impl Iterator<Item = TypeMarkerElem> + 'a {
        use ty::*;
        let def_id = match key.kind() {
            Adt(def, _) => Some(def.did()),
            Alias(_, inner) => Some(inner.def_id),
            _ => None,
        };
        def_id
            .map(|def_id| {
                self.combined_markers(def_id)
                    .map(move |m| (def_id, m.marker))
            })
            .into_iter()
            .flatten()
    }

    pub fn deep_type_markers<'a>(&'a self, key: ty::Ty<'tcx>) -> &'a TypeMarkers {
        self.0
            .type_markers
            .get_maybe_recursive(&key, |key| {
                use ty::*;
                let mut markers = self.shallow_type_markers(key).collect::<FxHashSet<_>>();
                let dcx = self.tcx().dcx();
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
                    | Coroutine(..)
                    | CoroutineWitness(..)
                    | CoroutineClosure(..)
                    | Never
                    | Bound { .. }
                    | Error(_) => (),
                    Adt(def, generics) => markers.extend(self.type_markers_for_adt(def, generics)),
                    Tuple(tys) => {
                        markers.extend(tys.iter().flat_map(|ty| self.deep_type_markers(ty)))
                    }
                    Alias(_, _) => {
                        dcx.warn(format!("Alias type {key:?} remains. Was not normalized."));
                        return Box::new([]);
                    }
                    Pat(ty, _) => {
                        return self.deep_type_markers(*ty).into();
                    }
                    // We can't track indices so we simply overtaint to the entire array
                    Array(inner, _) | Slice(inner) => {
                        markers.extend(self.deep_type_markers(*inner))
                    }
                    RawPtr(ty, _) | Ref(_, ty, _) => markers.extend(self.deep_type_markers(*ty)),
                    Param(_) | Dynamic { .. } => {
                        dcx.warn(format!("Cannot determine markers for type {key:?}"))
                    }
                    Placeholder(_) | Infer(_) => {
                        dcx.fatal(format!("Did not expect this type here {key:?}"))
                    }
                }
                markers.into_iter().collect()
            })
            .map_or(&[], Box::as_ref)
    }

    fn type_markers_for_adt<'a>(
        &'a self,
        adt: &'a ty::AdtDef<'tcx>,
        generics: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ) -> impl Iterator<Item = &'a TypeMarkerElem> {
        let tcx = self.tcx();
        adt.variants()
            .iter_enumerated()
            .flat_map(move |(_, vdef)| {
                vdef.fields.iter_enumerated().flat_map(move |(_, fdef)| {
                    let f_ty = fdef.ty(tcx, generics);
                    self.deep_type_markers(f_ty)
                })
            })
            .collect::<Vec<_>>()
            .into_iter()
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
        function: MaybeMonomorphized<'tcx>,
    ) -> impl Iterator<Item = (&'a MarkerAnnotation, Option<(ty::Ty<'tcx>, DefId)>)> {
        // Markers not coming from types, hence the "None"
        let direct_markers = self
            .combined_markers(function.def_id())
            .zip(std::iter::repeat(None));
        let get_type_markers = || {
            // TODO check soundness, especially for the closures
            let sig = match function {
                MaybeMonomorphized::Monomorphized(instance) => instance.sig(self.tcx()).ok(),
                MaybeMonomorphized::Plain(defid) => {
                    match FunctionKind::for_def_id(self.tcx(), defid).ok()? {
                        FunctionKind::Closure | FunctionKind::Generator => None,
                        _ => Some(self.tcx().fn_sig(defid).skip_binder().skip_binder()),
                    }
                }
            }?;
            let output = sig.output();
            // XXX I'm not entirely sure this is how we should do
            // this. For now I'm calling this "okay" because it's
            // basically the old behavior
            if output.is_closure() || output.is_coroutine() {
                return None;
            }
            Some(
                self.all_type_markers(output)
                    .map(|(marker, typeinfo)| (marker, Some(typeinfo))),
            )
        };

        direct_markers.chain(get_type_markers().into_iter().flatten())
    }

    /// Iterate over all discovered annotations, whether local or external
    pub fn all_annotations(
        &self,
    ) -> impl Iterator<Item = (DefId, Either<&Annotation, &MarkerAnnotation>)> {
        self.source_annotations_found()
            .into_iter()
            .flat_map(|(key, anns)| anns.iter().map(move |a| (key, Either::Left(a))))
            .chain(
                self.0
                    .external_annotations
                    .iter()
                    .flat_map(|(&id, anns)| anns.iter().map(move |ann| (id, Either::Right(ann)))),
            )
    }

    pub fn functions_seen(&self) -> Vec<MaybeMonomorphized<'tcx>> {
        let cache = self.0.reachable_markers.borrow();
        cache.keys().copied().collect::<Vec<_>>()
    }

    pub fn has_stub(&self, def_id: DefId) -> Option<&'static Stub> {
        [def_id]
            .into_iter()
            .chain(
                matches!(self.tcx().def_kind(def_id), DefKind::AssocFn)
                    .then(|| self.tcx().associated_item(def_id).trait_item_def_id)
                    .flatten(),
            )
            .find_map(|def_id| self.0.stubs.get(&def_id))
            .copied()
    }
}

pub type TypeMarkerElem = (DefId, Identifier);
pub type TypeMarkers = [TypeMarkerElem];

/// Either we have an [`Instance`] or a [`DefId`] if we weren't able to resolve
/// the generics.
///
/// This is only used so that we can reuse the code that finds reachable markers.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum MaybeMonomorphized<'tcx> {
    Monomorphized(Instance<'tcx>),
    Plain(DefId),
}

impl<'tcx> MaybeMonomorphized<'tcx> {
    pub fn def_id(&self) -> DefId {
        match self {
            MaybeMonomorphized::Monomorphized(instance) => instance.def_id(),
            MaybeMonomorphized::Plain(did) => *did,
        }
    }

    pub fn args(&self) -> Option<GenericArgsRef<'tcx>> {
        match self {
            MaybeMonomorphized::Monomorphized(instance) => Some(instance.args),
            _ => None,
        }
    }

    pub fn is_monomorphized(&self) -> bool {
        matches!(self, Self::Monomorphized(_))
    }
}

impl From<DefId> for MaybeMonomorphized<'_> {
    fn from(value: DefId) -> Self {
        Self::Plain(value)
    }
}

impl<'tcx> From<Instance<'tcx>> for MaybeMonomorphized<'tcx> {
    fn from(value: Instance<'tcx>) -> Self {
        Self::Monomorphized(value)
    }
}

/// The structure inside of [`MarkerCtx`].
pub struct MarkerDatabase<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Cache for parsed local annotations. They are created with
    /// [`MarkerCtx::retrieve_local_annotations_for`].
    annotations: FxHashMap<DefId, Vec<Annotation>>,
    external_annotations: ExternalMarkers,
    /// Cache whether markers are reachable transitively.
    reachable_markers: Cache<MaybeMonomorphized<'tcx>, Box<[Identifier]>>,
    /// Configuration options
    config: &'static Args,
    type_markers: Cache<ty::Ty<'tcx>, Box<TypeMarkers>>,
    body_cache: Rc<BodyCache<'tcx>>,
    included_crates: FxHashSet<CrateNum>,
    stubs: FxHashMap<DefId, &'static Stub>,
}

impl<'tcx> MarkerDatabase<'tcx> {
    /// Construct a new database, loading external markers.
    pub fn init(
        tcx: TyCtxt<'tcx>,
        args: &'static Args,
        body_cache: Rc<BodyCache<'tcx>>,
        included_crates: FxHashSet<CrateNum>,
    ) -> Self {
        let stubs = args
            .build_config()
            .stubs
            .iter()
            .filter_map(|(k, v)| {
                let res = expect_resolve_string_to_def_id(tcx, k, args.relaxed());
                let res = if args.relaxed() { res? } else { res.unwrap() };
                Some((res, v))
            })
            .collect();
        Self {
            tcx,
            annotations: load_annotations(tcx, included_crates.iter().copied()),
            external_annotations: resolve_external_markers(args, tcx),
            reachable_markers: Default::default(),
            config: args,
            type_markers: Default::default(),
            body_cache,
            included_crates,
            stubs,
        }
    }
}

fn load_annotations(
    tcx: TyCtxt,
    included_crates: impl IntoIterator<Item = CrateNum>,
) -> FxHashMap<DefId, Vec<Annotation>> {
    included_crates
        .into_iter()
        .flat_map(|krate| {
            let paths = local_or_remote_paths(krate, tcx, MARKER_META_EXT);
            for path in &paths {
                let Ok(mut file) = File::open(path) else {
                    continue;
                };
                let mut buf = Vec::new();
                file.read_to_end(&mut buf).unwrap();
                let mut decoder = ParalegalDecoder::new(tcx, buf.as_slice());
                let meta = MarkerMeta::decode(&mut decoder);
                return meta
                    .into_iter()
                    .map(move |(index, v)| (DefId { krate, index }, v));
            }
            panic!("No marker metadata fund for crate {krate}, tried paths {paths:?}");
        })
        .collect()
}

#[derive(serde::Deserialize)]
struct ExternalAnnotationEntry {
    marker: Option<Identifier>,
    #[serde(default)]
    markers: Vec<Identifier>,
    #[serde(flatten)]
    refinement: MarkerRefinement,
    #[serde(default)]
    refinements: Vec<MarkerRefinement>,
}

impl ExternalAnnotationEntry {
    fn flatten(&self) -> impl Iterator<Item = MarkerAnnotation> + '_ {
        let refinement_iter = self
            .refinements
            .iter()
            .chain(self.refinements.is_empty().then_some(&self.refinement));
        self.marker
            .into_iter()
            .chain(self.markers.iter().copied())
            .flat_map(move |marker| {
                refinement_iter
                    .clone()
                    .map(move |refinement| MarkerAnnotation {
                        marker,
                        refinement: refinement.clone(),
                    })
            })
    }

    fn check_integrity(&self, tcx: TyCtxt, element: DefId) {
        let merror = if self.marker.is_none() && self.markers.is_empty() {
            Some("neither")
        } else if self.marker.is_some() && !self.markers.is_empty() {
            Some("both")
        } else {
            None
        };
        if let Some(complaint) = merror {
            tcx.dcx().err(format!("External marker annotation should specify either a 'marker' or a 'markers' field, found {complaint} for {}", tcx.def_path_str(element)));
        }
        if !self.refinement.on_self() && !self.refinements.is_empty() {
            tcx.dcx().err(format!("External marker annotation should specify either a single refinement or the 'refinements' field, found both for {}", tcx.def_path_str(element)));
        }
    }
}

type RawExternalMarkers = HashMap<String, Vec<ExternalAnnotationEntry>>;

/// Given the TOML of external annotations we have parsed, resolve the paths
/// (keys of the map) to [`DefId`]s.
fn resolve_external_markers(opts: &Args, tcx: TyCtxt) -> ExternalMarkers {
    let relaxed = opts.relaxed();
    if let Some(annotation_file) = opts.marker_control().external_annotations() {
        let from_toml: RawExternalMarkers = toml::from_str(
            &std::fs::read_to_string(annotation_file).unwrap_or_else(|_| {
                panic!(
                    "Could not open file {}",
                    annotation_file
                        .canonicalize()
                        .unwrap_or_else(|_| annotation_file.to_path_buf())
                        .display()
                )
            }),
        )
        .unwrap();
        let new_map: ExternalMarkers = from_toml
            .iter()
            .filter_map(|(path, entries)| {
                let def_id = expect_resolve_string_to_def_id(tcx, path, relaxed)?;
                let markers = entries
                    .iter()
                    .flat_map(|entry| {
                        entry.check_integrity(tcx, def_id);
                        entry.flatten()
                    })
                    .collect();
                Some((def_id, markers))
            })
            .collect();
        new_map
    } else {
        HashMap::new()
    }
}
