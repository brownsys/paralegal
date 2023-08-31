//! Type definitions and helper functions for a Forge-friendly representation of
//! flow analysis results and annotations we discovered.
//!
//! Analyses that create these types are in [`ana`](crate::ana) and serializers for
//! emitting forge from them in [`crate::frg`].
//!
//! The top-level type is [`ProgramDescription`]

#![cfg_attr(feature = "rustc", feature(rustc_private))]

#[cfg(feature = "rustc")]
extern crate rustc_driver;
#[cfg(feature = "rustc")]
extern crate rustc_hir;
#[cfg(feature = "rustc")]
extern crate rustc_middle;
#[cfg(feature = "rustc")]
extern crate rustc_span;

#[cfg(feature = "rustc")]
mod rustc;
#[cfg(feature = "rustc")]
use self::rustc::*;
use indexical::define_index_type;
#[cfg(feature = "rustc")]
use rustc_hir::{self as hir, def_id};
#[cfg(feature = "rustc")]
use rustc_middle::mir;

pub mod tiny_bitset;

use crate::tiny_bitset::TinyBitSet;
use internment::Intern;
use log::warn;
use serde::{Deserialize, Serialize};
use std::{fmt, hash::Hash};

pub use std::collections::{HashMap, HashSet};

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Serialize, Deserialize)]
#[cfg_attr(feature = "rustc", serde(remote = "mir::BasicBlock"))]
pub struct BasicBlock {
    #[cfg_attr(feature = "rustc", serde(getter = "bbref_to_usize"))]
    private: usize,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Serialize, Deserialize)]
#[cfg_attr(feature = "rustc", serde(remote = "mir::Location"))]
pub struct Location {
    #[cfg(feature = "rustc")]
    #[serde(with = "BasicBlock")]
    pub block: mir::BasicBlock,
    #[cfg(not(feature = "rustc"))]
    pub block: BasicBlock,
    pub statement_index: usize,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Serialize, Deserialize)]
#[cfg_attr(feature = "rustc", serde(remote = "hir::ItemLocalId"))]
pub struct ItemLocalId {
    #[cfg_attr(feature = "rustc", serde(getter = "item_local_id_as_u32"))]
    private: u32,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Serialize, Deserialize)]
#[cfg_attr(feature = "rustc", serde(remote = "def_id::DefIndex"))]
struct DefIndex {
    #[cfg_attr(feature = "rustc", serde(getter = "def_index_as_u32"))]
    private: u32,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Serialize, Deserialize)]
#[cfg_attr(feature = "rustc", serde(remote = "def_id::LocalDefId"))]
struct LocalDefId {
    #[cfg(feature = "rustc")]
    #[serde(with = "DefIndex")]
    local_def_index: def_id::DefIndex,
    #[cfg(not(feature = "rustc"))]
    local_def_index: DefIndex,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Serialize, Deserialize)]
#[cfg_attr(feature = "rustc", serde(remote = "hir::hir_id::OwnerId"))]
struct OwnerId {
    #[cfg(feature = "rustc")]
    #[serde(with = "LocalDefId")]
    def_id: def_id::LocalDefId,
    #[cfg(not(feature = "rustc"))]
    def_id: LocalDefId,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Serialize, Deserialize)]
#[cfg_attr(feature = "rustc", serde(remote = "hir::HirId"))]
struct HirId {
    #[cfg(feature = "rustc")]
    #[serde(with = "OwnerId")]
    owner: hir::OwnerId,
    #[cfg(not(feature = "rustc"))]
    owner: OwnerId,
    #[cfg(feature = "rustc")]
    #[serde(with = "ItemLocalId")]
    local_id: hir::ItemLocalId,
    #[cfg(not(feature = "rustc"))]
    local_id: ItemLocalId,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Serialize, Deserialize)]
#[cfg_attr(feature = "rustc", serde(remote = "hir::BodyId"))]
pub struct BodyId {
    #[cfg(feature = "rustc")]
    #[serde(with = "HirId")]
    hir_id: hir::HirId,
    #[cfg(not(feature = "rustc"))]
    hir_id: HirId,
}

pub type Endpoint = Identifier;
pub type TypeDescriptor = Identifier;
pub type Function = Identifier;

/// Types of annotations we support.
///
/// Usually you'd expect one of those annotation types in any given situation.
/// For convenience the match methods [`Self::as_label_ann`],
/// [`Self::as_otype_ann`] and [`Self::as_exception_annotation`] are provided. These are particularly useful in conjunction with e.g. [`Iterator::filter_map`]
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, serde::Deserialize, serde::Serialize)]
pub enum Annotation {
    Label(MarkerAnnotation),
    OType(Vec<TypeDescriptor>),
    Exception(ExceptionAnnotation),
}

impl Annotation {
    pub fn as_label_ann(&self) -> Option<&MarkerAnnotation> {
        match self {
            Annotation::Label(l) => Some(l),
            _ => None,
        }
    }

    pub fn is_label_ann(&self) -> bool {
        matches!(self, Annotation::Label(_))
    }

    pub fn as_otype_ann(&self) -> Option<&[TypeDescriptor]> {
        match self {
            Annotation::OType(t) => Some(t),
            _ => None,
        }
    }

    pub fn as_exception_annotation(&self) -> Option<&ExceptionAnnotation> {
        match self {
            Annotation::Exception(e) => Some(e),
            _ => None,
        }
    }
}

pub type VerificationHash = u128;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ExceptionAnnotation {
    /// The value of the verification hash we found in the annotation. Is `None`
    /// if there was no verification hash in the annotation.
    pub verification_hash: Option<VerificationHash>,
}

/// A label annotation and its refinements.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct MarkerAnnotation {
    /// The (unchanged) name of the label as provided by the user
    pub marker: Identifier,
    #[serde(flatten)]
    pub refinement: MarkerRefinement,
}

fn const_false() -> bool {
    false
}

/// Refinements in the label targeting. The default (no refinement provided) is
/// `on_argument == vec![]` and `on_return == false`, which is also what is
/// returned from [`Self::empty`].
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, serde::Deserialize, serde::Serialize)]
pub struct MarkerRefinement {
    #[serde(default, with = "crate::tiny_bitset::pretty")]
    on_argument: TinyBitSet,
    #[serde(default = "const_false")]
    on_return: bool,
}

/// Refinements as the parser discovers them. Are then merged onto the aggregate [`AnnotationRefinement`] with [`AnnotationRefinement::merge_kind`].
#[derive(Clone, serde::Deserialize, serde::Serialize)]
pub enum MarkerRefinementKind {
    /// Corresponds to [`AnnotationRefinement::on_argument`]
    Argument(#[serde(with = "crate::tiny_bitset::pretty")] TinyBitSet),
    /// Corresponds to [`AnnotationRefinement::on_return`]
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

    pub fn on_argument(&self) -> TinyBitSet {
        self.on_argument
    }

    pub fn on_return(&self) -> bool {
        self.on_return
    }

    /// True if this refinement is empty, i.e. the annotation is targeting the
    /// item itself.
    pub fn on_self(&self) -> bool {
        self.on_argument.is_empty() && !self.on_return
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum ObjectType {
    Function(usize),
    Type,
    Other,
}

impl ObjectType {
    pub fn is_function(&self) -> Option<usize> {
        match self {
            ObjectType::Function(f) => Some(*f),
            _ => None,
        }
    }
    pub fn merge(&mut self, other: &Self) {
        if self != other {
            warn!(
                "Merging two different object types {:?} and {:?}!",
                self, other
            );
            match (self, other) {
                (ObjectType::Function(ref mut i), ObjectType::Function(j)) => {
                    if j > i {
                        *i = *j
                    }
                }
                (slf, other) => {
                    panic!("Cannot merge two different object types {slf:?} and {other:?}")
                }
            }
        }
    }
    pub fn is_type(&self) -> bool {
        matches!(self, ObjectType::Type)
    }
}

pub type AnnotationMap = HashMap<Identifier, (Vec<Annotation>, ObjectType)>;

/// A Forge friendly representation of the dataflow graphs we calculated and the
/// annotations we found.
#[derive(Serialize, Deserialize, Debug)]
pub struct ProgramDescription {
    pub controllers: HashMap<Endpoint, Ctrl>,
    pub annotations: AnnotationMap,
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
    pub fn all_sources_with_ctrl(&self) -> HashSet<(Identifier, &DataSource)> {
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
    pub fn all_functions(&self) -> HashSet<&Identifier> {
        self.all_call_sites()
            .into_iter()
            .map(|cs| &cs.function)
            .chain(
                self.annotations
                    .iter()
                    .filter(|f| f.1 .1.is_function().is_some())
                    .map(|f| f.0),
            )
            .collect()
    }
}

#[derive(Hash, Eq, PartialEq, Ord, Debug, PartialOrd, Clone, Serialize, Deserialize, Copy)]
pub struct Identifier(Intern<String>);

impl Identifier {
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    pub fn new_intern(s: &str) -> Self {
        Identifier(Intern::from_ref(s))
    }
}

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.0.fmt(f)
    }
}

/// Because we need these kinds of associations so often I made a separate type
/// for it. Also allows us to serialize it more conveniently.
#[derive(Debug)]
pub struct Relation<X, Y>(pub HashMap<X, HashSet<Y>>);

impl<X: serde::Serialize, Y: serde::Serialize + std::hash::Hash + std::cmp::Eq> serde::Serialize
    for Relation<X, Y>
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.iter().collect::<Vec<_>>().serialize(serializer)
    }
}

impl<
        'de,
        X: serde::Deserialize<'de> + std::hash::Hash + std::cmp::Eq,
        Y: serde::Deserialize<'de> + std::hash::Hash + std::cmp::Eq,
    > serde::Deserialize<'de> for Relation<X, Y>
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        <Vec<_> as serde::Deserialize<'de>>::deserialize(deserializer)
            .map(|v| Self(v.into_iter().collect()))
    }
}

impl<X, Y> Relation<X, Y> {
    pub fn empty() -> Self {
        Relation(HashMap::new())
    }
}

/// The payload type of a global location. You will probably want to operate on
/// the interned wrapper type [`GlobalLocation`], which gives access to the same
/// fields with methods such as [`function`](IsGlobalLocation::function),
/// [`location`](IsGlobalLocation::location) and
/// [`next`](IsGlobalLocation::next).
///
/// Other methods and general information for global locations is documented on
/// [`GlobalLocation`].
///
/// The generic parameter `Inner` is typically instantiated recursively with the
/// interned wrapper type `GlobalLocation<'g>`, forming an interned linked list.
/// We use a generic parameter so that deserializers can instead instantiate
/// them as [`GlobalLocationS`], i.e. a non-interned version of the same struct.
/// This is necessary because in the derived deserializers we do not have access
/// to the interner.
///
/// For convenience the trait [`IsGlobalLocation`] is provided which lets you
/// operate directly on the wrapper types and also na way that works with any
/// global location type (both [`GlobalLocation`] as well as the serializable
/// [`crate::serializers::RawGlobalLocation`])
#[derive(PartialEq, Eq, Hash, Debug, Clone, Deserialize, Serialize, Copy)]
pub struct GlobalLocationS {
    #[cfg(feature = "rustc")]
    #[serde(with = "BodyId")]
    /// The id of the body in which this location is located.
    pub function: hir::BodyId,
    #[cfg(not(feature = "rustc"))]
    /// The id of the body in which this location is located.
    pub function: BodyId,
    #[cfg(feature = "rustc")]
    #[serde(with = "Location")]
    /// The location itself
    pub location: mir::Location,
    #[cfg(not(feature = "rustc"))]
    /// The location itself
    pub location: Location,
}
/// A serializable non-interned version of [`GlobalLocation`].
///
/// Thanks to the [`IsGlobalLocation`] trait you can use this the same way as a
/// [`GlobalLocation`]. Though be aware that this struct is significantly larger
/// in memory as it contains a singly-linked list of call chains that is not
/// interned.
///
/// For information on the meaning of this struct see [`GlobalLocation`]
#[derive(Deserialize, Serialize, PartialEq, Eq, Hash, Clone, Debug)]
pub struct RawGlobalLocation(pub Vec<GlobalLocationS>);

pub fn write_sep<
    E,
    I: IntoIterator<Item = E>,
    F: FnMut(E, &mut fmt::Formatter<'_>) -> fmt::Result,
>(
    fmt: &mut fmt::Formatter<'_>,
    sep: &str,
    it: I,
    mut f: F,
) -> fmt::Result {
    let mut first = true;
    for e in it {
        if first {
            first = false;
        } else {
            fmt.write_str(sep)?;
        }
        f(e, fmt)?;
    }
    Ok(())
}

/// Formatting for global locations that works independent of whether it is an
/// interned or inlined location.
pub fn format_global_location<'a>(
    t: impl DoubleEndedIterator<Item = &'a GlobalLocationS>,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    write_sep(f, "@", t.rev(), |elem, f| {
        write!(
            f,
            "{:?}[{}]",
            elem.location.block, elem.location.statement_index
        )
    })?;
    Ok(())
}

impl std::fmt::Display for RawGlobalLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        format_global_location(self.0.iter(), f)
    }
}

/// [`GlobalLocation`](crate::ir::GlobalLocation).
#[derive(Hash, Eq, PartialEq, Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct CallSite {
    pub location: RawGlobalLocation,
    pub function: Function,
}

/// Create a hash for this object that is no longer than six hex digits
pub fn short_hash_pls<T: Hash>(t: T) -> u64 {
    // Six digits in hex
    hash_pls(t) % 0x1_000_000
}

/// Calculate a hash for this object
pub fn hash_pls<T: Hash>(t: T) -> u64 {
    use std::hash::Hasher;
    let mut hasher = std::collections::hash_map::DefaultHasher::default();
    t.hash(&mut hasher);
    hasher.finish()
}

impl std::string::ToString for CallSite {
    fn to_string(&self) -> String {
        format!(
            "cs_{}_{:x}",
            self.function.as_str(),
            short_hash_pls(&self.location),
        )
    }
}

/// A representation of something that can emit data into the flow.
///
/// Convenience match functions are provided (for use e.g. in
/// [`Iterator::filter_map`]) with [`Self::as_function_call`] and [`Self::as_argument`].
#[derive(Hash, Eq, PartialEq, Clone, serde::Serialize, serde::Deserialize, Debug)]
pub enum DataSource {
    /// The result of a function call in the controller body. Can be the return
    /// value or a mutable argument that was passed to the call.
    FunctionCall(CallSite),
    /// An argument to the controller function.
    Argument(usize),
}

define_index_type! {
    pub struct DataSourceIndex for DataSource = u32;
}

impl DataSource {
    pub fn as_function_call(&self) -> Option<&CallSite> {
        match self {
            DataSource::FunctionCall(i) => Some(i),
            _ => None,
        }
    }
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
#[derive(Hash, PartialEq, Eq, Clone, serde::Serialize, serde::Deserialize, Debug)]
pub enum DataSink {
    Argument { function: CallSite, arg_slot: usize },
    Return,
}

impl DataSink {
    pub fn as_argument(&self) -> Option<(&CallSite, usize)> {
        match self {
            DataSink::Argument { function, arg_slot } => Some((function, *arg_slot)),
            _ => None,
        }
    }
}

define_index_type! {
    pub struct DataSinkIndex for DataSink = u32;
}

/// Annotations on types in a controller. Only types that have annotations are
/// present in this map, meaning that it is guaranteed that for any key `k`
/// `map.get(k).is_empty() == false`.
pub type CtrlTypes = Relation<DataSource, TypeDescriptor>;

#[derive(Deserialize, Serialize, Debug)]
pub struct Ctrl {
    pub data_flow: Relation<DataSource, DataSink>,
    pub ctrl_flow: Relation<DataSource, CallSite>,
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
    /// Extend the type annotations
    pub fn add_types<I: IntoIterator<Item = (DataSource, HashSet<TypeDescriptor>)>>(
        &mut self,
        i: I,
    ) {
        i.into_iter().for_each(|(ident, set)| {
            self.types
                .0
                .entry(ident)
                .or_insert_with(HashSet::new)
                .extend(set.into_iter())
        })
    }

    pub fn with_input_types(types: CtrlTypes) -> Self {
        Ctrl {
            data_flow: Relation::empty(),
            ctrl_flow: Relation::empty(),
            types,
        }
    }
    pub fn add_data_flow(&mut self, from: std::borrow::Cow<DataSource>, to: DataSink) {
        let m = &mut self.data_flow.0;
        if let Some(e) = m.get_mut(&from) {
            e.insert(to);
        } else {
            m.insert(from.into_owned(), std::iter::once(to).collect());
        }
    }
    pub fn add_ctrl_flow(&mut self, from: std::borrow::Cow<DataSource>, to: CallSite) {
        let m = &mut self.ctrl_flow.0;
        if let Some(e) = m.get_mut(&from) {
            e.insert(to);
        } else {
            m.insert(from.into_owned(), std::iter::once(to).collect());
        }
    }

    pub fn data_sinks(&self) -> impl Iterator<Item = &DataSink> + '_ {
        self.data_flow.0.values().flatten()
    }
}
