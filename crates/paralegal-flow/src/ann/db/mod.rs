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
    ann::{
        db::reachable::marker_if_unloadable, side_effect_detection, Annotation,
        ExceptionAnnotation, MarkerAnnotation,
    },
    args::{Args, Stub},
    utils::{is_function_like, resolve::expect_resolve_string_to_def_id, IntoDefId},
    Either, HashMap,
};
use flowistry::mir::FlowistryInput;
use flowistry_pdg_construction::source_access::{
    local_or_remote_paths, BodyCache, ParalegalDecoder,
};
use itertools::Itertools;
use paralegal_spdg::{Identifier, TypeId};

use rustc_data_structures::fx::FxHashMap;
use rustc_errors::DiagMessage;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_hir::{def::DefKind, def_id::CrateNum};
use rustc_middle::{
    mir::Local,
    ty::{self, GenericArgsRef, Instance, Ty, TyCtxt},
};
use rustc_serialize::Decodable;

use rustc_span::Span;
use rustc_utils::cache::Cache;

use anyhow::Context;
use serde::Deserialize;
use serde_json::json;

use std::{
    cell::{RefCell, RefMut},
    fs::File,
    io::Read,
    rc::Rc,
};

use super::{MarkerMeta, MarkerRefinement, MARKER_META_EXT};

mod reachable;
mod type_markers;

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
    pub(super) fn tcx(&self) -> TyCtxt<'tcx> {
        self.0.tcx
    }

    #[inline]
    pub(super) fn db(&self) -> &MarkerDatabase<'tcx> {
        &self.0
    }

    // /// All markers reachable for this item (local and external).
    // ///
    // /// Queries are cached/precomputed so calling this repeatedly is cheap.
    // fn known_markers<'s>(
    //     &'s self,
    //     def_id: DefId,
    //     selector: MarkerSelector,
    // ) -> impl Iterator<Item = MarkerAnnotation> + use<'s> {
    //     self.source_annotations(def_id)
    //         .iter()
    //         .filter_map(Annotation::as_marker)
    //         .chain(self.external_markers(def_id))
    //         .copied()
    //         .chain({
    //             // To avoid calling "fn_sig" for constructors and other non-functions
    //             let (markers, arg_len) = if self.0.config.marker_control().mark_side_effects()
    //                 && is_function_like(self.tcx(), def_id)
    //             {
    //                 let sig = self.tcx().fn_sig(def_id);
    //                 let arg_len = sig.skip_binder().inputs().skip_binder().len() as u32;
    //                 (self.side_effect_markers(def_id), arg_len)
    //             } else {
    //                 (&[] as _, 0)
    //             };
    //             markers.iter().map(move |m| MarkerAnnotation {
    //                 marker: *m,
    //                 refinement: MarkerRefinement {
    //                     on_argument: (0..arg_len).into(),
    //                     on_return: true,
    //                 },
    //             })
    //         })
    // }

    pub fn side_effect_markers(&self, def_id: DefId) -> &[Identifier] {
        if !is_function_like(self.tcx(), def_id) {
            return &[];
        }
        if let Some(m) = marker_if_unloadable(self.tcx(), def_id, self.auto_markers()) {
            return std::slice::from_ref(m);
        }
        if !self.crate_is_included(def_id.krate) {
            return &[];
        }
        self.db().side_effect_heuristics_results.get(&def_id, |_| {
            let body = self.db().body_cache.get(def_id).body();
            side_effect_detection::analyze_body(body, &self.db().auto_markers, self.tcx())
                .into_iter()
                .collect()
        })
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

    /// Are there any markers (local or external) on this item?
    ///
    /// This is in contrast to [`Self::marker_is_reachable`] which also reports
    /// if markers are reachable from the body of this function (if it is one).
    pub fn is_marked<D: IntoDefId + Copy>(&self, did: D) -> bool {
        let defid = did.into_def_id(self.tcx());
        self.0
            .markers
            .get(&defid)
            .is_some_and(|markers| !markers.is_empty())
    }

    pub fn all_markers_associated_with<'a>(
        &'a self,
        defid: DefId,
    ) -> impl Iterator<Item = Identifier> + use<'a> {
        self.0
            .markers
            .get(&defid)
            .into_iter()
            .flat_map(|markers| markers.values())
            .flat_map(|v| v.iter().copied())
    }

    pub fn markers_on_self(&self, defid: DefId) -> &[Identifier] {
        (|| self.0.markers.get(&defid)?.get(&MarkerSelector::Item))().map_or(&[], Vec::as_slice)
    }

    pub fn marker_count(&self) -> usize {
        self.0.markers.values().map(|markers| markers.len()).sum()
    }

    pub fn markers_on_argument(&self, defid: DefId, arg: u16) -> &[Identifier] {
        (|| {
            self.0
                .markers
                .get(&defid)?
                .get(&MarkerSelector::Argument(arg))
        })()
        .map_or(&[], Vec::as_slice)
    }

    pub fn markers_on_return(&self, defid: DefId) -> &[Identifier] {
        (|| self.0.markers.get(&defid)?.get(&MarkerSelector::Return))().map_or(&[], Vec::as_slice)
    }

    // /// Return a complete set of local annotations that were discovered.
    // ///
    // /// Crucially this is a "readout" from the marker cache, which means only
    // /// items reachable from the `paralegal_flow::analyze` will end up in this collection.
    // pub fn source_annotations_found(&self) -> Vec<(DefId, &[Annotation])> {
    //     self.db()
    //         .annotations
    //         .iter()
    //         .map(|(k, v)| (*k, v.as_slice()))
    //         .collect()
    // }

    /// Are there markers reachable from this (function)?
    ///
    /// Returns true if the item itself carries a marker *or* if one of the
    /// functions called in its body are marked.
    ///
    /// XXX Does not take into account reachable type markers
    pub fn marker_is_reachable(&self, res: Instance<'tcx>) -> bool {
        self.is_marked(res.def_id()) || self.has_transitive_reachable_markers(res)
    }

    pub(super) fn borrow_function_marker_stat(
        &self,
        key: MaybeMonomorphized<'tcx>,
    ) -> RefMut<'_, FunctionMarkerStat<'tcx>> {
        RefMut::map(self.0.marker_statistics.borrow_mut(), |r| {
            r.entry(key).or_insert_with(|| FunctionMarkerStat {
                function: key,
                is_constructor: self.tcx().is_constructor(key.def_id()),
                is_async: None,
                is_stubbed: None,
                markers_from_variables: vec![],
                markers_on_self: vec![],
                calls_with_reachable_markers: vec![],
            })
        })
    }

    pub(super) fn span_err(&self, span: Span, msg: impl Into<DiagMessage>) {
        if self.0.config.relaxed() {
            self.tcx().dcx().span_warn(span, msg.into());
        } else {
            self.tcx().dcx().span_err(span, msg.into());
        }
    }

    pub fn auto_markers(&self) -> &AutoMarkers {
        &self.0.auto_markers
    }

    #[allow(unused)]
    fn err(&self, msg: impl Into<DiagMessage>) {
        if self.0.config.relaxed() {
            self.tcx().dcx().warn(msg.into());
        } else {
            self.tcx().dcx().err(msg.into());
        }
    }

    // /// All markers placed on this function, directly or through the type plus
    // /// the type that was marked (if any).
    // pub fn all_function_markers<'a>(
    //     &'a self,
    //     function: MaybeMonomorphized<'tcx>,
    // ) -> impl Iterator<Item = (MarkerAnnotation, Option<(ty::Ty<'tcx>, DefId)>)> + use<'a, 'tcx>
    // {
    //     // Markers not coming from types, hence the "None"
    //     let direct_markers = self
    //         .combined_markers(function.def_id())
    //         .zip(std::iter::repeat(None));
    //     let get_type_markers = || {
    //         // TODO check soundness, especially for the closures
    //         let sig = match function {
    //             MaybeMonomorphized::Monomorphized(instance) => instance.sig(self.tcx()).ok(),
    //             MaybeMonomorphized::Plain(defid) => {
    //                 match FunctionKind::for_def_id(self.tcx(), defid).ok()? {
    //                     FunctionKind::Closure | FunctionKind::Generator => None,
    //                     _ => Some(self.tcx().fn_sig(defid).skip_binder().skip_binder()),
    //                 }
    //             }
    //         }?;
    //         let output = sig.output();
    //         // XXX I'm not entirely sure this is how we should do
    //         // this. For now I'm calling this "okay" because it's
    //         // basically the old behavior
    //         if output.is_closure() || output.is_coroutine() {
    //             return None;
    //         }
    //         Some(
    //             self.all_type_markers(output)
    //                 .map(|(marker, typeinfo)| (marker, Some(typeinfo))),
    //         )
    //     };

    //     direct_markers.chain(get_type_markers().into_iter().flatten())
    // }

    /// Iterate over all discovered annotations, whether local or external
    pub fn all_annotations<'a>(&'a self) -> impl Iterator<Item = (DefId, Annotation)> + use<'a> {
        self.0
            .other_annotations
            .iter()
            .flat_map(|(k, v)| {
                std::iter::repeat(*k).zip(
                    v.iter()
                        .map(|e| e.clone().either(Annotation::OType, Annotation::Exception)),
                )
            })
            .chain(
                self.0
                    .markers
                    .iter()
                    .flat_map(|(k, vs)| std::iter::repeat(*k).zip(recreate_refinements(vs.iter())))
                    .map(|(def_id, refinement)| (def_id, Annotation::Marker(refinement))),
            )
    }

    pub fn all_markers_on_item<'a>(
        &'a self,
        def_id: DefId,
    ) -> impl Iterator<Item = MarkerAnnotation> + use<'a> {
        self.0
            .markers
            .get(&def_id)
            .into_iter()
            .flat_map(|i| recreate_refinements(i))
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

    pub fn dump_marker_stats(&self, mut f: impl std::io::Write) {
        serde_json::to_writer(
            &mut f,
            &marker_stats_as_json(self.tcx(), self.0.marker_statistics.borrow().values()),
        )
        .unwrap()
    }

    pub fn crate_is_included(&self, krate: CrateNum) -> bool {
        (self.0.included_crates)(krate)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
enum MarkerSelector {
    Item,
    Argument(u16),
    Return,
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
    other_annotations: FxHashMap<DefId, Vec<Either<TypeId, ExceptionAnnotation>>>,
    markers: FxHashMap<DefId, HashMap<MarkerSelector, Vec<Identifier>>>,
    /// Cache whether markers are reachable transitively.
    reachable_markers: Cache<MaybeMonomorphized<'tcx>, Box<[Identifier]>>,
    /// Configuration options
    config: &'static Args,
    type_markers: Cache<ty::Ty<'tcx>, Box<TypeMarkers>>,
    body_cache: Rc<BodyCache<'tcx>>,
    included_crates: Rc<dyn Fn(CrateNum) -> bool>,
    stubs: FxHashMap<DefId, &'static Stub>,
    marker_statistics: RefCell<HashMap<MaybeMonomorphized<'tcx>, FunctionMarkerStat<'tcx>>>,
    auto_markers: AutoMarkers,
    side_effect_heuristics_results: Cache<DefId, Box<[Identifier]>>,
}

pub struct AutoMarkers {
    pub side_effect_unknown_virtual: Identifier,
    pub side_effect_foreign: Identifier,
    pub side_effect_unknown_fn_ptr: Identifier,
    pub side_effect_raw_ptr: Identifier,
    pub side_effect_transmute: Identifier,
    pub side_effect_unknown: Identifier,
}

impl AutoMarkers {
    pub fn new() -> Self {
        AutoMarkers {
            side_effect_unknown_virtual: Identifier::new_intern("auto:side-effect:unknown:virtual"),
            side_effect_foreign: Identifier::new_intern("auto:side-effect:foreign"),
            side_effect_unknown_fn_ptr: Identifier::new_intern("auto:side-effect:unknown:fn-ptr"),
            side_effect_raw_ptr: Identifier::new_intern("auto:side-effect:raw-ptr"),
            side_effect_transmute: Identifier::new_intern("auto:side-effect:transmute"),
            side_effect_unknown: Identifier::new_intern("auto:side-effect:unknown"),
        }
    }

    pub fn all(&self) -> [Identifier; 6] {
        [
            self.side_effect_unknown_virtual,
            self.side_effect_foreign,
            self.side_effect_unknown_fn_ptr,
            self.side_effect_raw_ptr,
            self.side_effect_transmute,
            self.side_effect_unknown,
        ]
    }
}

pub struct FunctionMarkerStat<'tcx> {
    pub function: MaybeMonomorphized<'tcx>,
    pub is_constructor: bool,
    pub is_async: Option<Instance<'tcx>>,
    pub is_stubbed: Option<Instance<'tcx>>,
    pub markers_from_variables: Vec<(Local, Ty<'tcx>, Vec<Identifier>)>,
    pub markers_on_self: Vec<Identifier>,
    pub calls_with_reachable_markers: Vec<(MaybeMonomorphized<'tcx>, Span)>,
}

fn marker_stats_as_json<'tcx: 'a, 'a>(
    tcx: TyCtxt<'tcx>,
    i: impl IntoIterator<Item = &'a FunctionMarkerStat<'tcx>>,
) -> serde_json::Value {
    i.into_iter()
        .map(|stat| {
            let mm_to_json = |mm: MaybeMonomorphized<'_>| {
                json!({
                    "ident": tcx.def_path_str(mm.def_id()),
                    "args": match mm {
                        MaybeMonomorphized::Plain(_) => serde_json::Value::Null,
                        MaybeMonomorphized::Monomorphized(instance) => {
                            json!(instance.args.iter().map(|a| a.to_string()).collect::<Vec<_>>())
                        }
                    }
                })
            };
            let instance_to_json = |instance: Instance<'tcx>|
                json!({
                    "ident": tcx.def_path_str(instance.def_id()),
                    "args": instance.args.iter().map(|a| a.to_string()).collect::<Vec<_>>()
                });
            json!({
                "function": mm_to_json(stat.function),
                "is_constructor": stat.is_constructor,
                "is_async": stat.is_async.map(instance_to_json),
                "is_stubbed": stat.is_stubbed.map(instance_to_json),
                "markers_from_variables": stat.markers_from_variables.iter().map(|(l, ty, markers)| {
                    json!({
                        "local": format!("{l:?}"),
                        "type": format!("{ty:?}"),
                        "markers": markers
                    })
                }).collect::<Vec<_>>(),
                "markers_on_self": stat.markers_on_self,
                "calls_with_reachable_markers": stat.calls_with_reachable_markers.iter().map(|(mm, span)| {
                    json!({
                        "function": mm_to_json(*mm),
                        "span": format!("{span:?}")
                    })
                }).collect::<Vec<_>>()
            })
        }).collect()
}

impl<'tcx> MarkerDatabase<'tcx> {
    /// Construct a new database, loading external markers.
    pub fn init(tcx: TyCtxt<'tcx>, args: &'static Args, body_cache: Rc<BodyCache<'tcx>>) -> Self {
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
        let included_crates = Rc::new(args.anactrl().inclusion_predicate(tcx));
        let local_annotations = load_annotations(
            tcx,
            args.anactrl().included_crates(tcx).chain([LOCAL_CRATE]),
        );
        let external_markers = resolve_external_markers(args, tcx);
        let mut other_annotations: FxHashMap<_, Vec<_>> = FxHashMap::default();
        let mut markers: FxHashMap<DefId, HashMap<MarkerSelector, Vec<Identifier>>> =
            external_markers
                .into_iter()
                .map(|(item, anns)| (item, annotations_to_grouped_map(anns)))
                .collect();
        for (item, anns) in local_annotations {
            for ann in anns {
                match ann {
                    Annotation::Marker(r) => {
                        for s in refinement_to_selectors(r.refinement) {
                            markers
                                .entry(item)
                                .or_default()
                                .entry(s)
                                .or_default()
                                .push(r.marker);
                        }
                    }
                    Annotation::OType(o) => {
                        other_annotations
                            .entry(item)
                            .or_default()
                            .push(Either::Left(o));
                    }
                    Annotation::Exception(e) => {
                        other_annotations
                            .entry(item)
                            .or_default()
                            .push(Either::Right(e));
                    }
                }
            }
        }
        Self {
            other_annotations,
            markers,
            included_crates,
            stubs,
            ..Self::init_no_markers(tcx, args, body_cache)
        }
    }

    /// Initialize a new context without loading any annotations or external
    /// markers and only selecting the local crate for analysis.
    pub fn init_no_markers(
        tcx: TyCtxt<'tcx>,
        opts: &'static crate::Args,
        body_cache: Rc<BodyCache<'tcx>>,
    ) -> Self {
        Self {
            tcx,
            other_annotations: FxHashMap::default(),
            markers: HashMap::default(),
            reachable_markers: Default::default(),
            config: opts,
            type_markers: Default::default(),
            body_cache,
            included_crates: Rc::new(|f| f == LOCAL_CRATE),
            stubs: FxHashMap::default(),
            marker_statistics: RefCell::new(HashMap::default()),
            auto_markers: AutoMarkers::new(),
            side_effect_heuristics_results: Default::default(),
        }
    }
}

fn refinement_to_selectors(refinement: MarkerRefinement) -> impl Iterator<Item = MarkerSelector> {
    refinement
        .on_argument
        .into_iter_set_in_domain()
        .map(|i| MarkerSelector::Argument(i as u16))
        .chain(refinement.on_return.then_some(MarkerSelector::Return))
        .chain(refinement.on_self().then_some(MarkerSelector::Item))
}

fn annotations_to_grouped_map(
    i: impl IntoIterator<Item = super::MarkerAnnotation>,
) -> HashMap<MarkerSelector, Vec<Identifier>> {
    i.into_iter()
        .flat_map(|super::MarkerAnnotation { marker, refinement }| {
            refinement_to_selectors(refinement).map(move |selector| (selector, marker))
        })
        .into_group_map()
}

fn recreate_refinements<'a, I: IntoIterator<Item = (&'a MarkerSelector, &'a Vec<Identifier>)>>(
    selectors: I,
) -> impl Iterator<Item = super::MarkerAnnotation> + use<'a, I> {
    selectors
        .into_iter()
        .flat_map(|(selector, markers)| markers.into_iter().map(move |marker| (*marker, selector)))
        .into_grouping_map()
        .fold(
            MarkerRefinement {
                on_return: false,
                on_argument: Default::default(),
            },
            |mut acc, _, selector| {
                match selector {
                    MarkerSelector::Argument(a) => acc.on_argument.set(*a as u32),
                    MarkerSelector::Return => acc.on_return = true,
                    _ => (),
                }
                acc
            },
        )
        .into_iter()
        .map(|(marker, refinement)| super::MarkerAnnotation { marker, refinement })
}

fn load_annotations(
    tcx: TyCtxt,
    included_crates: impl IntoIterator<Item = CrateNum>,
) -> FxHashMap<DefId, Vec<Annotation>> {
    let sysroot = &tcx.sess.sysroot;
    included_crates
        .into_iter()
        .flat_map(|krate| {
            let paths = local_or_remote_paths(krate, tcx, MARKER_META_EXT);
            for path in &paths {
                if path.starts_with(sysroot) {
                    return Either::Left(std::iter::empty());
                }
                let Ok(mut file) = File::open(path) else {
                    continue;
                };
                let mut buf = Vec::new();
                file.read_to_end(&mut buf).unwrap();
                let mut decoder = ParalegalDecoder::new(tcx, buf.as_slice());
                let meta = MarkerMeta::decode(&mut decoder);
                return Either::Right(
                    meta.into_iter()
                        .map(move |(index, v)| (DefId { krate, index }, v)),
                );
            }
            panic!("No marker metadata found for crate {krate}, tried paths {paths:?}");
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

fn check_format(from_toml: &toml::Value) -> anyhow::Result<()> {
    use anyhow::bail;
    let Some(table) = from_toml.as_table() else {
        bail!("External annotations must be a table");
    };
    for (key, v) in table {
        let Some(arr) = v.as_array() else {
            bail!("External annotation entry for `{key}` must be an array");
        };
        for (i, entry) in arr.iter().enumerate() {
            let Some(e) = entry.as_table() else {
                bail!("External annotation entry for `{key}.[{i}]` must be a table");
            };
            for k in e.keys() {
                if k != "marker"
                    && k != "markers"
                    && k != "on_argument"
                    && k != "on_return"
                    && k != "refinements"
                {
                    bail!("External annotation entry for `{key}.[{i}]` may only have `marker`, `markers`, `on_argument`, `on_return` or `refinements` fields");
                }
            }
        }
    }
    Ok(())
}

fn parse_external_marker_file(s: &str) -> anyhow::Result<RawExternalMarkers> {
    let from_toml = toml::from_str(s)?;
    check_format(&from_toml)?;

    Ok(RawExternalMarkers::deserialize(
        serde::de::IntoDeserializer::into_deserializer(from_toml),
    )?)
}

/// Given the TOML of external annotations we have parsed, resolve the paths
/// (keys of the map) to [`DefId`]s.
fn resolve_external_markers(opts: &Args, tcx: TyCtxt) -> ExternalMarkers {
    //let relaxed = opts.relaxed();
    let relaxed = false;
    if let Some(annotation_file) = opts.marker_control().external_annotations() {
        let data = std::fs::read_to_string(annotation_file).unwrap_or_else(|_| {
            panic!(
                "Could not open file {}",
                annotation_file
                    .canonicalize()
                    .unwrap_or_else(|_| annotation_file.to_path_buf())
                    .display()
            )
        });
        let from_toml = parse_external_marker_file(&data)
            .with_context(|| {
                anyhow::anyhow!(
                    "When parsing external annotation file {}",
                    annotation_file.display()
                )
            })
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

#[cfg(test)]
mod test {
    use crate::ann::db::parse_external_marker_file;

    #[test]
    fn test_parse_marker_file() {
        let examples = [
            (
                "[[\"std::vec::Vec\"]]
                marker = \"test\"",
                true,
            ),
            (
                "[[\"std::vec::Vec\"]]
                marker = \"test\"
                on_return = true",
                true,
            ),
            (
                "[[\"std::vec::Vec\"]]
                marker = \"test\"
                on_argument = [0]",
                true,
            ),
            (
                "[[\"std::vec::Vec\"]]
                marker = \"test\"
                on_argument = [0]
                on_return = true",
                true,
            ),
            // Technically this should also fail, but we don't check this
            // property during deserialization, but later
            // (
            //     "[[\"std::vec::Vec\"]]
            //     on_argument = [0]",
            //     false,
            // ),
            (
                "[[\"std::vec::Vec\"]]
                marker = \"test\"
                on-argument = [0]
                on_return = true",
                false,
            ),
            (
                "[[\"std::vec::Vec\"]]
                marker = \"test\"
                on_argument = [0]
                on-return = true",
                false,
            ),
            (
                "[[\"std::vec::Vec\"]]
                marker = \"test\"
                on_argument = [0]
                on_return = true
                extra = []",
                false,
            ),
        ];

        for (input, expected) in examples {
            let ret = parse_external_marker_file(input);
            assert_eq!(
                ret.is_ok(),
                expected,
                "Expected {input} to {}, but {}",
                if expected { "succeed" } else { "fail" },
                match ret {
                    Ok(_) => "succeeded".to_string(),
                    Err(e) => format!("failed with error: {}", e),
                }
            );
        }
    }
}
