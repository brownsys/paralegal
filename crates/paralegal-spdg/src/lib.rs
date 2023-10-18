//! This crate defines the program dependence graph (PDG) generated by Paralegal.
//!
//! The top-level type is [`ProgramDescription`]. This type references multiple
//! types defined within the Rust compiler such as MIR locations. To avoid requiring
//! a `rustc_private` dependency on paralegal_spdg clients, we provide proxies in the
//! [`rustc_proxies`] module for all Rustc types within the PDG.

#![cfg_attr(feature = "rustc", feature(rustc_private))]
#![warn(missing_docs)]

#[cfg(feature = "rustc")]
pub(crate) mod rustc {
    extern crate rustc_driver;
    pub extern crate rustc_hir as hir;
    pub extern crate rustc_index as index;
    pub extern crate rustc_middle as middle;
    pub extern crate rustc_span as span;
    pub use hir::def_id;
    pub use middle::mir;
}

pub mod global_location;
#[cfg(feature = "rustc")]
mod rustc_impls;
pub mod rustc_portable;
pub mod rustc_proxies;
mod tiny_bitset;
pub mod utils;

use global_location::GlobalLocation;
use indexical::define_index_type;
use internment::Intern;
use itertools::Itertools;
use rustc_portable::DefId;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{borrow::Cow, fmt, hash::Hash, iter};

#[cfg(not(feature = "rustc"))]
use utils::serde_map_via_vec;

pub use crate::tiny_bitset::TinyBitSet;
pub use std::collections::{HashMap, HashSet};

pub type Endpoint = DefId;
pub type TypeDescriptor = DefId;
pub type Function = Identifier;

/// Name of the file used for emitting the JSON serialized
/// [`ProgramDescription`](crate::ProgramDescription).
pub const FLOW_GRAPH_OUT_NAME: &str = "flow-graph.json";

/// Types of annotations we support.
///
/// Usually you'd expect one of those annotation types in any given situation.
/// For convenience the match methods [`Self::as_marker`], [`Self::as_otype`]
/// and [`Self::as_exception`] are provided. These are particularly useful in
/// conjunction with e.g. [`Iterator::filter_map`]
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Deserialize, Serialize, strum::EnumIs)]
pub enum Annotation {
    Marker(MarkerAnnotation),
    OType(#[cfg_attr(feature = "rustc", serde(with = "rustc_proxies::DefId"))] TypeDescriptor),
    Exception(ExceptionAnnotation),
}

impl Annotation {
    /// If this is an [`Annotation::Marker`], returns the underlying [`MarkerAnnotation`].
    pub fn as_marker(&self) -> Option<&MarkerAnnotation> {
        match self {
            Annotation::Marker(l) => Some(l),
            _ => None,
        }
    }

    /// If this is an [`Annotation::OType`], returns the underlying [`TypeDescriptor`].
    pub fn as_otype(&self) -> Option<TypeDescriptor> {
        match self {
            Annotation::OType(t) => Some(*t),
            _ => None,
        }
    }

    /// If this is an [`Annotation::Exception`], returns the underlying [`ExceptionAnnotation`].
    pub fn as_exception(&self) -> Option<&ExceptionAnnotation> {
        match self {
            Annotation::Exception(e) => Some(e),
            _ => None,
        }
    }
}

pub type VerificationHash = u128;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Serialize, Deserialize)]
pub struct ExceptionAnnotation {
    /// The value of the verification hash we found in the annotation. Is `None`
    /// if there was no verification hash in the annotation.
    pub verification_hash: Option<VerificationHash>,
}

/// A marker annotation and its refinements.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Serialize, Deserialize)]
pub struct MarkerAnnotation {
    /// The (unchanged) name of the marker as provided by the user
    pub marker: Identifier,
    #[serde(flatten)]
    pub refinement: MarkerRefinement,
}

fn const_false() -> bool {
    false
}

/// Refinements in the marker targeting. The default (no refinement provided) is
/// `on_argument == vec![]` and `on_return == false`, which is also what is
/// returned from [`Self::empty`].
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Deserialize, Serialize)]
pub struct MarkerRefinement {
    #[serde(default, with = "crate::tiny_bitset::pretty")]
    on_argument: TinyBitSet,
    #[serde(default = "const_false")]
    on_return: bool,
}

/// Disaggregated version of [`MarkerRefinement`]. Can be added to an existing
/// refinement [`MarkerRefinement::merge_kind`].
#[derive(Clone, Deserialize, Serialize)]
pub enum MarkerRefinementKind {
    Argument(#[serde(with = "crate::tiny_bitset::pretty")] TinyBitSet),
    Return,
}

impl MarkerRefinement {
    /// The default, empty aggregate refinement `Self { on_argument: vec![],
    /// on_return: false }`
    pub fn empty() -> Self {
        Self {
            on_argument: Default::default(),
            on_return: false,
        }
    }

    /// Merge the aggregate refinement with another discovered refinement and
    /// check that they do not overwrite each other.
    pub fn merge_kind(mut self, k: MarkerRefinementKind) -> Result<Self, String> {
        match k {
            MarkerRefinementKind::Argument(a) => {
                if self.on_argument.is_empty() {
                    self.on_argument = a;
                    Ok(self)
                } else {
                    Err(format!(
                        "Double argument annotation {:?} and {a:?}",
                        self.on_argument
                    ))
                }
            }
            MarkerRefinementKind::Return => {
                if !self.on_return {
                    self.on_return = true;
                    Ok(self)
                } else {
                    Err("Double on-return annotation".to_string())
                }
            }
        }
    }

    /// Get the refinements on arguments
    pub fn on_argument(&self) -> TinyBitSet {
        self.on_argument
    }

    /// Is this refinement targeting the return value?
    pub fn on_return(&self) -> bool {
        self.on_return
    }

    /// True if this refinement is empty, i.e. the annotation is targeting the
    /// item itself.
    pub fn on_self(&self) -> bool {
        self.on_argument.is_empty() && !self.on_return
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Serialize, Deserialize, strum::EnumIs)]
pub enum ObjectType {
    Function(usize),
    Type,
    Other,
}

impl ObjectType {
    /// If this is [`Self::Function`], then return the payload.
    pub fn as_function(&self) -> Option<usize> {
        match self {
            ObjectType::Function(f) => Some(*f),
            _ => None,
        }
    }
}

pub type AnnotationMap = HashMap<DefId, (Vec<Annotation>, ObjectType)>;

#[cfg(feature = "rustc")]
mod ser_defid_map {
    use serde::{Deserialize, Serialize};

    use crate::rustc_proxies;

    #[derive(Serialize, Deserialize)]
    struct Helper(#[serde(with = "rustc_proxies::DefId")] super::DefId);

    pub fn serialize<S: serde::Serializer, V: serde::Serialize>(
        map: &super::HashMap<super::DefId, V>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        map.iter()
            .map(|(k, v)| (Helper(*k), v))
            .collect::<Vec<_>>()
            .serialize(serializer)
    }

    pub fn deserialize<'de, D: serde::Deserializer<'de>, V: serde::Deserialize<'de>>(
        deserializer: D,
    ) -> Result<super::HashMap<super::DefId, V>, D::Error> {
        Ok(Vec::deserialize(deserializer)?
            .into_iter()
            .map(|(Helper(k), v)| (k, v))
            .collect())
    }
}

/// Exported information from rustc about what sort of object a [`DefId`] points
/// to.
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize, Debug)]
pub struct DefInfo {
    /// Name of the object. Usually the one that a user assigned, but can be
    /// generated in the case of closures and generators
    pub name: Identifier,
    /// Def path to the object
    pub path: Vec<Identifier>,
    /// Kind of object
    pub kind: DefKind,
}

/// Similar to `DefKind` in rustc but *not the same*!
#[derive(Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Debug, strum::EnumIs, strum::AsRefStr)]
pub enum DefKind {
    Fn,
    Generator,
    Closure,
    Type,
}

/// The annotated program dependence graph.
#[derive(Serialize, Deserialize, Debug)]
pub struct ProgramDescription {
    #[cfg_attr(feature = "rustc", serde(with = "ser_defid_map"))]
    #[cfg_attr(not(feature = "rustc"), serde(with = "serde_map_via_vec"))]
    /// Mapping from function names to dependencies within the function.
    pub controllers: HashMap<Endpoint, Ctrl>,

    #[cfg_attr(not(feature = "rustc"), serde(with = "serde_map_via_vec"))]
    #[cfg_attr(feature = "rustc", serde(with = "ser_defid_map"))]
    /// Mapping from objects to annotations on those objects.
    pub annotations: AnnotationMap,

    #[cfg_attr(not(feature = "rustc"), serde(with = "serde_map_via_vec"))]
    #[cfg_attr(feature = "rustc", serde(with = "ser_defid_map"))]
    /// Metadata about the `DefId`s
    pub def_info: HashMap<DefId, DefInfo>,
}

impl ProgramDescription {
    /// Gather all [`DataSource`]s that are mentioned in this program description.
    ///
    /// Essentially just `self.controllers.flat_map(|c| c.keys())`
    pub fn all_sources(&self) -> HashSet<&DataSource> {
        self.controllers
            .values()
            .flat_map(|c| {
                c.data_flow
                    .0
                    .keys()
                    .chain(c.types.0.keys())
                    .chain(c.ctrl_flow.0.keys())
            })
            .collect()
    }
    /// Gather all [`DataSource`]s that are mentioned in this program description.
    ///
    /// Essentially just `self.controllers.flat_map(|c| c.keys())`
    pub fn all_sources_with_ctrl(&self) -> HashSet<(DefId, &DataSource)> {
        self.controllers
            .iter()
            .flat_map(|(name, c)| {
                c.data_flow
                    .0
                    .keys()
                    .chain(c.types.0.keys())
                    .chain(c.ctrl_flow.0.keys())
                    .map(|ds| (*name, ds))
            })
            .collect()
    }
    /// Gather all [`DataSink`]s mentioned in this program description
    ///
    /// Essentially just `self.controllers.flat_map(|c| c.values())`
    pub fn all_sinks(&self) -> HashSet<&DataSink> {
        self.controllers
            .values()
            .flat_map(|ctrl| ctrl.data_flow.0.values().flat_map(|v| v.iter()))
            .collect()
    }

    /// Gather all [`CallSite`]s that are mentioned in this program description.
    ///
    /// This function is a bit more subtle than [`Self::all_sinks`] and
    /// [`Self::all_sources`] (which are simple maps), because call sites occur
    /// in more places. So this extracts the call sites from sources as well as
    /// sinks.
    pub fn all_call_sites(&self) -> HashSet<&CallSite> {
        self.controllers
            .values()
            .flat_map(|ctrl| {
                ctrl.data_flow
                    .0
                    .values()
                    .flat_map(|v| v.iter().filter_map(DataSink::as_argument).map(|s| s.0))
                    .chain(
                        ctrl.data_flow
                            .0
                            .keys()
                            .filter_map(|src| src.as_function_call()),
                    )
                    .chain(
                        ctrl.ctrl_flow
                            .0
                            .keys()
                            .filter_map(|src| src.as_function_call()),
                    )
                    .chain(ctrl.ctrl_flow.0.values().flat_map(|v| v.iter()))
            })
            .collect()
    }

    /// Gather all function identifiers that are mentioned in this program description.
    ///
    /// Essentially just `self.all_call_sites().map(|cs| cs.function)`
    pub fn all_functions(&self) -> HashSet<DefId> {
        self.all_call_sites()
            .into_iter()
            .map(|cs| cs.function)
            .chain(
                self.annotations
                    .iter()
                    .filter(|f| f.1 .1.as_function().is_some())
                    .map(|f| *f.0),
            )
            .collect()
    }
}

/// An identifier for any kind of object (functions, markers, etc.).
///
/// Implemented as an interned string, so identifiers are cheap to reuse.
#[derive(Hash, Eq, PartialEq, Ord, PartialOrd, Clone, Serialize, Deserialize, Copy)]
pub struct Identifier(Intern<String>);

impl Identifier {
    /// Returns the underlying string from an identifier.
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// Interns the input string into an identifier.
    ///
    /// Note: this requires locking the global intern arena. See [`internment::Intern`] for details.
    pub fn new_intern(s: &str) -> Self {
        Identifier(Intern::from_ref(s))
    }
}

impl std::fmt::Debug for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        std::fmt::Debug::fmt(&self.0.as_ref(), f)
    }
}

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.0.as_ref().fmt(f)
    }
}

impl<'a> From<&'a str> for Identifier {
    fn from(value: &'a str) -> Self {
        Self::new_intern(value)
    }
}

/// Because we need these kinds of associations so often I made a separate type
/// for it. Also allows us to serialize it more conveniently.
#[derive(Debug)]
pub struct Relation<X, Y>(pub HashMap<X, HashSet<Y>>);

impl<X, Y> std::ops::Deref for Relation<X, Y> {
    type Target = HashMap<X, HashSet<Y>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<X, Y> std::ops::DerefMut for Relation<X, Y> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<X: Serialize, Y: Serialize + Hash + Eq> Serialize for Relation<X, Y> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.iter().collect::<Vec<_>>().serialize(serializer)
    }
}

impl<'de, X: Deserialize<'de> + Hash + Eq, Y: Deserialize<'de> + Hash + Eq> Deserialize<'de>
    for Relation<X, Y>
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        <Vec<_> as Deserialize<'de>>::deserialize(deserializer)
            .map(|v| Self(v.into_iter().collect()))
    }
}

impl<X, Y> Relation<X, Y> {
    /// Constructs an empty relation.
    pub fn empty() -> Self {
        Relation(HashMap::new())
    }
}

/// A global location in the program where a function is being called.
#[derive(Hash, Eq, PartialEq, Clone, Debug, Serialize, Deserialize)]
pub struct CallSite {
    /// The location of the call.
    pub location: GlobalLocation,

    #[cfg_attr(feature = "rustc", serde(with = "rustc_proxies::DefId"))]
    /// The id of the function being called.
    pub function: DefId,
}

impl std::fmt::Display for CallSite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.location.fmt(f)
    }
}

define_index_type! {
    /// Index over [`CallSite`], for use with `indexical` index sets.
    pub struct CallSiteIndex for CallSite = u32;
}

// Either CallSite or DataSink type
#[derive(Hash, Eq, PartialEq, Clone, Debug, Serialize, Deserialize)]
pub enum CallSiteOrDataSink {
    CallSite(CallSite),
    DataSink(DataSink),
}

impl CallSiteOrDataSink {
    pub fn as_call_site(&self) -> Option<&CallSite> {
        match self {
            Self::CallSite(cs) => Some(cs),
            _ => None,
        }
    }

    pub fn as_data_sink(&self) -> Option<&DataSink> {
        match self {
            Self::DataSink(ds) => Some(ds),
            _ => None,
        }
    }
}

impl From<CallSite> for CallSiteOrDataSink {
    fn from(value: CallSite) -> Self {
        CallSiteOrDataSink::CallSite(value)
    }
}

impl From<DataSink> for CallSiteOrDataSink {
    fn from(value: DataSink) -> Self {
        CallSiteOrDataSink::DataSink(value)
    }
}

define_index_type! {
    /// Index over [`CallSite`], for use with `indexical` index sets.
    pub struct CallSiteOrDataSinkIndex for CallSiteOrDataSink = u32;
}

/// Create a hash for this object that is no longer than six hex digits
///
/// The intent for this is to be used as a pre- or postfix to make a non-unique
/// name for the object `T` unique. The [`fmt::Display`] implementation should be
/// used for canonical formatting.
#[derive(Debug, Clone, Copy)]
pub struct ShortHash(u64);

impl ShortHash {
    pub fn new<T: Hash>(t: T) -> Self {
        // Six digits in hex
        Self(hash_pls(t) % 0x1_000_000)
    }
}

impl fmt::Display for ShortHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:06x}", self.0)
    }
}

#[test]
fn short_hash_always_six_digits() {
    assert_eq!(format!("{}", ShortHash(0x0)).len(), 6);
    assert_eq!(format!("{}", ShortHash(0x57110)).len(), 6);
}

/// Calculate a hash for this object
fn hash_pls<T: Hash>(t: T) -> u64 {
    use std::hash::Hasher;
    let mut hasher = std::collections::hash_map::DefaultHasher::default();
    t.hash(&mut hasher);
    hasher.finish()
}

// impl std::string::ToString for CallSite {
//     fn to_string(&self) -> String {
//         format!(
//             "cs_{}_{}",
//             self.function.as_str(),
//             ShortHash::new(self.location),
//         )
//     }
// }

/// A representation of something that can emit data into the flow.
///
/// Convenience match functions are provided (for use e.g. in
/// [`Iterator::filter_map`]) with [`Self::as_function_call`] and [`Self::as_argument`].
#[derive(Hash, Eq, PartialEq, Clone, Serialize, Deserialize, Debug)]
pub enum DataSource {
    /// The result of a function call in the controller body. Can be the return
    /// value or a mutable argument that was passed to the call.
    FunctionCall(CallSite),

    /// An argument to the controller function.
    Argument(usize),
}

impl std::fmt::Display for DataSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DataSource::Argument(a) => write!(f, "a{a}"),
            DataSource::FunctionCall(cs) => cs.fmt(f),
        }
    }
}

define_index_type! {
    /// Index over [`DataSource`], for use with `indexical` index sets.
    pub struct DataSourceIndex for DataSource = u32;
}

impl DataSource {
    /// If this is a [`DataSource::FunctionCall`], then returns the underlying [`CallSite`].
    pub fn as_function_call(&self) -> Option<&CallSite> {
        match self {
            DataSource::FunctionCall(i) => Some(i),
            _ => None,
        }
    }

    /// If this is a [`DataSource::Argument`], then returns the underlying argument index.
    pub fn as_argument(&self) -> Option<usize> {
        match self {
            DataSource::Argument(a) => Some(*a),
            _ => None,
        }
    }
}

/// A representation of something that can receive data from the flow.
///
/// [`Self::as_argument`] is provided for convenience of matching.
#[derive(Hash, PartialEq, Eq, Clone, Serialize, Deserialize, Debug)]
pub enum DataSink {
    Argument { function: CallSite, arg_slot: usize },
    Return,
}

impl DataSink {
    /// If this is a `DataSink::Argument`, then returns that branch's fields.
    pub fn as_argument(&self) -> Option<(&CallSite, usize)> {
        match self {
            DataSink::Argument { function, arg_slot } => Some((function, *arg_slot)),
            _ => None,
        }
    }
}

impl std::fmt::Display for DataSink {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DataSink::Return => f.write_str("return"),
            DataSink::Argument { function, arg_slot } => write!(f, "a{arg_slot} of {function}"),
        }
    }
}

define_index_type! {
    /// Index over [`DataSink`], for use with `indexical` index sets.
    pub struct DataSinkIndex for DataSink = u32;
}

pub type CtrlTypes = Relation<DataSource, TypeDescriptor>;

#[cfg(feature = "rustc")]
mod ser_ctrl_types {
    use serde::{Deserialize, Serialize};

    use crate::rustc_proxies;

    #[derive(Serialize, Deserialize)]
    struct Helper(#[serde(with = "rustc_proxies::DefId")] super::DefId);

    pub fn serialize<S: serde::Serializer>(
        map: &super::CtrlTypes,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        map.iter()
            .map(|(k, v)| (k.clone(), v.iter().copied().map(Helper).collect::<Vec<_>>()))
            .collect::<Vec<_>>()
            .serialize(serializer)
    }

    pub fn deserialize<'de, D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> Result<super::CtrlTypes, D::Error> {
        Ok(crate::Relation(
            Vec::deserialize(deserializer)?
                .into_iter()
                .map(|(k, v): (_, Vec<_>)| (k, v.into_iter().map(|Helper(id)| id).collect()))
                .collect(),
        ))
    }
}

/// Dependencies within a controller function.
#[derive(Serialize, Deserialize, Debug)]
pub struct Ctrl {
    /// Non-transitive data dependencies between sources and sinks.
    pub data_flow: Relation<DataSource, DataSink>,

    /// Transitive control dependencies between sources and call sites.
    pub ctrl_flow: Relation<DataSource, CallSite>,

    #[cfg_attr(feature = "rustc", serde(with = "ser_ctrl_types"))]
    /// Annotations on types in a controller.
    ///
    /// Only types that have annotations are present in this map, meaning
    /// that it is guaranteed that for any key `k` that
    /// `map.get(k).is_empty() == false`.
    pub types: CtrlTypes,
}

impl Default for Ctrl {
    fn default() -> Self {
        Ctrl {
            data_flow: Relation::empty(),
            ctrl_flow: Relation::empty(),
            types: Relation::empty(),
        }
    }
}

impl Ctrl {
    /// Returns an iterator over all the data sinks in the `data_flow` relation.
    pub fn data_sinks(&self) -> impl Iterator<Item = &DataSink> + '_ {
        self.data_flow.0.values().flatten().unique()
    }

    /// Returns an iterator over all the callsites in the `ctrl_flow` relation.
    pub fn call_sites(&self) -> impl Iterator<Item = &CallSite> + '_ {
        self.ctrl_flow.0.values().flatten().unique()
    }

    /*** Below are constructor methods intended for use within paralegal-flow. ***/

    /// Extend the `types` map with the input iterator.
    pub fn add_types(
        &mut self,
        i: impl IntoIterator<Item = (DataSource, HashSet<TypeDescriptor>)>,
    ) {
        for (ident, set) in i {
            self.types.0.entry(ident).or_default().extend(set);
        }
    }

    /// Construct an empty controller with the given [`CtrlTypes`].
    pub fn with_input_types(types: CtrlTypes) -> Self {
        Ctrl {
            data_flow: Relation::empty(),
            ctrl_flow: Relation::empty(),
            types,
        }
    }

    /// Add one data flow between `from` and `to`.
    pub fn add_data_flow(&mut self, from: Cow<DataSource>, to: DataSink) {
        let m = &mut self.data_flow.0;
        if let Some(e) = m.get_mut(&from) {
            e.insert(to);
        } else {
            m.insert(from.into_owned(), iter::once(to).collect());
        }
    }

    /// Add one control flow between `from` and `to`.
    pub fn add_ctrl_flow(&mut self, from: Cow<DataSource>, to: CallSite) {
        let m = &mut self.ctrl_flow.0;
        if let Some(e) = m.get_mut(&from) {
            e.insert(to);
        } else {
            m.insert(from.into_owned(), iter::once(to).collect());
        }
    }

    /// Gather all [`DataSource`]s that are mentioned in this controller including data and control flow.
    pub fn all_sources(&self) -> HashSet<&DataSource> {
        self.data_flow
            .0
            .keys()
            .chain(self.types.0.keys())
            .chain(self.ctrl_flow.0.keys())
            .dedup()
            .collect()
    }

    /// Gather all [`DataSink`]s or [`CallSite`]s that are mentioned in this controller including data and control flow.
    pub fn all_call_sites_or_sinks(&self) -> impl Iterator<Item = CallSiteOrDataSink> + '_ {
        self.data_flow
            .0
            .values()
            .flatten()
            .flat_map(|s| {
                let as_or = CallSiteOrDataSink::DataSink(s.clone());
                match s {
                    DataSink::Argument { function, .. } => {
                        vec![CallSiteOrDataSink::CallSite(function.clone()), as_or]
                    }
                    _ => vec![as_or],
                }
            })
            .chain(
                self.ctrl_flow
                    .0
                    .values()
                    .flatten()
                    .map(|cs| CallSiteOrDataSink::CallSite(cs.clone())),
            )
            .dedup()
    }
}
