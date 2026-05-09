//! The representation of the PDG.

use std::{collections::HashMap, fmt};

use allocative::{ident_key, Allocative};
use internment::Intern;
use serde::{Deserialize, Serialize};

use crate::rustc_portable::*;
#[cfg(feature = "rustc")]
use crate::rustc_proxies;

/// Extends a MIR body's `Location` with `Start` (before the first instruction) and `End` (after all returns).
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Serialize, Deserialize)]
pub enum RichLocation {
    /// The point *after* a location in a body.
    #[cfg_attr(feature = "rustc", serde(with = "rustc_proxies::Location"))]
    Location(Location),

    /// The start of the body.
    ///
    /// Note that `Location::START` is different from [`RichLocation::Start`]!
    /// The latter is *before* the former in time.
    Start,

    /// The end of the body, after all possible return statements.
    End,
}

impl Allocative for RichLocation {
    fn visit<'a, 'b: 'a>(&self, visitor: &'a mut allocative::Visitor<'b>) {
        visitor.visit_simple_sized::<Self>();
    }
}

impl RichLocation {
    /// Returns true if this is a `Start` location.
    pub fn is_start(self) -> bool {
        matches!(self, RichLocation::Start)
    }

    /// Returns true if this is an `End` location.
    pub fn is_end(self) -> bool {
        matches!(self, RichLocation::End)
    }

    /// Returns true if this is a [`RichLocation::Location`] (i.e. not a
    /// synthetic `Start`/`End`).
    pub fn is_real(self) -> bool {
        matches!(self, RichLocation::Location(_))
    }

    /// Returns the [`Location`] in `self`, panicking otherwise.
    pub fn unwrap_location(self) -> Location {
        self.as_location()
            .expect("RichLocation was unexpectedly Start")
    }

    /// Returns the [`Location`] in `self`, returning `None` otherwise.
    pub fn as_location(self) -> Option<Location> {
        match self {
            RichLocation::Location(location) => Some(location),
            RichLocation::Start | RichLocation::End => None,
        }
    }
}

impl fmt::Display for RichLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RichLocation::Location(loc) => write!(f, "{loc:?}"),
            RichLocation::Start => write!(f, "start"),
            RichLocation::End => write!(f, "end"),
        }
    }
}

impl From<Location> for RichLocation {
    fn from(value: Location) -> Self {
        RichLocation::Location(value)
    }
}

/// A [`RichLocation`] within a specific point in a codebase.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Serialize, Deserialize, Allocative)]
pub struct GlobalLocation {
    /// The function containing the location.
    #[cfg_attr(feature = "rustc", serde(with = "rustc_proxies::DefId"))]
    #[allocative(visit = allocative_visit_simple_sized)]
    pub function: DefId,

    /// The location of an instruction in the function, or the function's start.
    pub location: RichLocation,
}

#[cfg(not(feature = "rustc"))]

impl fmt::Display for GlobalLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}::{}", self.function, self.location)
    }
}

/// A location within the global call-graph.
///
/// The first location is the root of the call-graph.
/// The last location is the currently-called function.
///
/// Invariant: a call string should never be empty, i.e.,
/// there should always be at least one [`GlobalLocation`] in a call-string.
///
/// Note: This type is copyable due to interning.
#[derive(PartialEq, Eq, Hash, Copy, Clone, Debug)]
pub struct CallString(Intern<CallStringInner>);

impl Allocative for CallString {
    fn visit<'a, 'b: 'a>(&self, visitor: &'a mut allocative::Visitor<'b>) {
        let mut visitor = visitor.enter_self_sized::<Self>();
        allocative_visit_intern_t(self.0, &mut visitor);
        visitor.exit();
    }
}

thread_local! {
    static TRACK_INTERN_AS_UNIQUE: bool = {
        if let Ok(val) = std::env::var("ALLOCATIVE_TRACK_INTERN_AS_UNIQUE") {
            val == "true" || val == "1"
        } else {
            false
        }
    }
}

/// Visitor adapter for [`Intern<T>`] used by `Allocative`.
///
/// Honours the `ALLOCATIVE_TRACK_INTERN_AS_UNIQUE` env var: when unset
/// (default) interned values are reported as shared so the same payload is
/// not double-counted across handles; when set, each `Intern` handle is
/// charged its full size.
pub fn allocative_visit_intern_t<T: Allocative + ?Sized>(
    intern: Intern<T>,
    visitor: &mut allocative::Visitor<'_>,
) {
    let track_as_unique = TRACK_INTERN_AS_UNIQUE.with(|v| *v);
    let ptr_size = std::mem::size_of::<*const T>();
    if !track_as_unique {
        let mut visitor = visitor.enter_self_sized::<Intern<T>>();
        {
            let ptr: &T = intern.as_ref();
            let as_ptr = ptr as *const T as *const ();

            let inner_visitor = visitor.enter_shared(ident_key!(intern_value), ptr_size, as_ptr);
            if let Some(mut visitor) = inner_visitor {
                ptr.visit(&mut visitor);
                visitor.exit();
            }
        }
        visitor.exit();
    } else {
        let mut visitor = visitor.enter_self_sized::<Intern<T>>();
        let inner: &T = intern.as_ref();
        {
            let mut visitor = visitor.enter_unique(ident_key!(pointee), ptr_size);
            inner.visit(&mut visitor);
            visitor.exit();
        }
        visitor.exit();
    }
}

impl Serialize for CallString {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.as_ref().serialize(serializer)
        // let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        // for loc in self.0.iter() {
        //     seq.serialize_element(loc)?;
        // }
        // seq.end()
    }
}

impl<'de> Deserialize<'de> for CallString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let locs = <Box<[GlobalLocation]>>::deserialize(deserializer)?;
        Ok(CallString::new(locs.as_ref()))
    }
}

type CallStringInner = [GlobalLocation];

impl CallString {
    /// Create a new call string from a list of global locations.
    pub fn new(locs: &CallStringInner) -> Self {
        CallString(Intern::from(locs))
    }

    /// Split the leaf (the current instruction) from the caller for the
    /// function (if any) and return both. Same as `(self.leaf(), self.caller())`.
    pub fn pop(self) -> (GlobalLocation, Option<CallString>) {
        let (last, rest) = self
            .0
            .split_last()
            .expect("Invariant broken, call strings must have at least length 1");

        (*last, (!rest.is_empty()).then(|| CallString::new(rest)))
    }

    /// Create an initial call string for the single location `loc`.
    pub fn single(loc: GlobalLocation) -> Self {
        Self::new(&[loc])
    }

    /// Returns the leaf of the call string (the currently-called function).
    pub fn leaf(self) -> GlobalLocation {
        *self.0.last().unwrap()
    }

    /// Returns the call string minus the leaf. Returns `None` if this location
    /// is at the root.
    pub fn caller(self) -> Option<Self> {
        self.pop().1
    }

    /// Returns an iterator over the locations in the call string, starting at
    /// the leaf and going to the root.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = GlobalLocation> + '_ {
        self.0.iter().rev().copied()
    }

    /// Adds a new call site to the end of the call string.
    pub fn push(self, loc: GlobalLocation) -> Self {
        let string = self.0.iter().copied().chain(Some(loc)).collect::<Box<_>>();
        CallString::new(&string)
    }

    /// Adds a new call site to the front (root) of the call string.
    pub fn push_front(self, loc: GlobalLocation) -> Self {
        CallString::new(
            [loc]
                .into_iter()
                .chain(self.0.iter().copied())
                .collect::<Box<_>>()
                .as_ref(),
        )
    }

    /// Returns true if this call string has a single (root) location.
    pub fn is_at_root(self) -> bool {
        self.0.len() == 1
    }

    /// Returns the root (outermost) location in the call string.
    pub fn root(self) -> GlobalLocation {
        *self.0.first().unwrap()
    }

    /// Returns an integer that uniquely identifies the interned backing
    /// storage. Stable across clones of the same [`CallString`]; suitable as
    /// a hashmap key when you need an opaque, copyable identity.
    pub fn stable_id(self) -> usize {
        let r: &'static CallStringInner = self.0.as_ref();
        r.as_ptr() as usize
    }

    /// Returns an iterator over the locations in the call string, starting at
    /// the root and going to the leaf.
    pub fn iter_from_root(&self) -> impl DoubleEndedIterator<Item = GlobalLocation> + '_ {
        self.0.iter().copied()
    }

    /// Number of locations in the call string.
    pub fn len(self) -> usize {
        self.0.len()
    }

    /// Returns true if the call string contains no locations.
    pub fn is_empty(self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Display for CallString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, loc) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, "←")?;
            }
            loc.fmt(f)?;
        }
        Ok(())
    }
}

/// A function that is fit to be handed to `#[allocative(visit = "...")]` for a
/// map where the key does not implement [`Allocative`], but also has no
/// attached heap data.
///
/// Uses [`SimpleSizedAllocativeWrapper`] under the hood, see its documentation
/// for more information.
pub fn allocative_visit_map_coerce_key<'a, K, V: Allocative>(
    map: &'a HashMap<K, V>,
    visitor: &mut allocative::Visitor<'a>,
) {
    let coerced: &HashMap<SimpleSizedAllocativeWrapper<K>, V> = unsafe { std::mem::transmute(map) };
    coerced.visit(visitor);
}

/// A function fit to be handed to `#[allocative(visit = "...")]`, if the type
/// does not have any attached heap data.
pub fn allocative_visit_simple_sized<T>(_: &T, visitor: &mut allocative::Visitor<'_>) {
    visitor.visit_simple_sized::<T>();
}

/// A wrapper that guarantees to be the same size as `T` and implements the
/// [`Allocative`] trait.
///
/// This uses [`allocative::Visitor::visit_simple_sized`] on `T` for sizing,
/// meaning that `T` will only be recorded with the size of the object itself,
/// *not* with its size in the heap.
///
/// The idea is that you can transmute any object of type `T` or any object that
/// *contains* `T` into one that is (or contains) `SimpleSizedAllocativeWrapper<T>`.
///
/// For example if you want the size of `HashMap<Unsupported, usize>` you can
/// `std::mem::transmute` it to
/// `HashMap<SimpleSizedAllocativeWrapper<Unsupported>, usize>` and then simply
/// ask for the size. However if there is attached heap data, liek in
/// `HashMap<UnsuportedString, usize>`, then the size reported will be incorrect.
#[repr(transparent)]
pub struct SimpleSizedAllocativeWrapper<T>(T);

impl<T> Allocative for SimpleSizedAllocativeWrapper<T> {
    fn visit<'a, 'b: 'a>(&self, visitor: &'a mut allocative::Visitor<'b>) {
        visitor.visit_simple_sized::<T>();
    }
}

/// A serialized representation of a MIR `Const` value.
///
/// Captures the kinds of constants the analyzer surfaces in PDG nodes; richer
/// forms (e.g. ADTs, references) are not tracked here.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy, Serialize, Deserialize)]
pub enum Constant {
    /// A signed integer constant.
    Int(i64),
    /// An unsigned integer constant.
    Uint(u64),
    /// A `char` constant.
    Char(char),
    // Placeholder. Floats in the rust compiler are a bit weird so I'll skip them for now.
    /// A floating-point constant. See [`FloatWrapper`] for the bit-equality
    /// caveat.
    Float(FloatWrapper),
    /// A boolean constant.
    Bool(bool),
    /// A string constant, interned to deduplicate identical literals.
    String(Intern<String>),
    //Unknown(Intern<String>),
    /// A zero-sized constant identified by its rendered type name (interned).
    Zst(Intern<String>),
}

/// This is an unsafe wrapper around f64 in that it defines hash and equality
/// based on bit representation. This is not in line with float semantics.
///
/// But I really need this to be hash and eq, hence the hack.
#[derive(Clone, Copy, Serialize, Deserialize, Debug)]
#[serde(transparent)]
pub struct FloatWrapper(pub f64);

impl std::cmp::PartialEq for FloatWrapper {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            std::mem::transmute::<&f64, &u64>(&self.0)
                == std::mem::transmute::<&f64, &u64>(&other.0)
        }
    }
}

impl std::cmp::Eq for FloatWrapper {}

impl std::hash::Hash for FloatWrapper {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe {
            std::mem::transmute::<&f64, &u64>(&self.0).hash(state);
        }
    }
}

impl Constant {
    /// Constructs a [`Constant::Int`] from anything convertible to `i64`.
    pub fn int(i: impl Into<i64>) -> Self {
        Self::Int(i.into())
    }
    /// Constructs a [`Constant::Uint`] from anything convertible to `u64`.
    pub fn uint(u: impl Into<u64>) -> Self {
        Self::Uint(u.into())
    }
    /// Constructs a [`Constant::Char`].
    pub fn char(c: impl Into<char>) -> Self {
        Self::Char(c.into())
    }
    /// Constructs a [`Constant::Bool`].
    pub fn bool(b: impl Into<bool>) -> Self {
        Self::Bool(b.into())
    }
    /// Constructs a [`Constant::String`], interning the contents.
    pub fn string(s: impl AsRef<str>) -> Self {
        Self::String(Intern::from_ref(s.as_ref()))
    }
    /// Constructs a [`Constant::Zst`] tagged with the given (interned) type name.
    pub fn zst(s: impl AsRef<str>) -> Self {
        Self::Zst(Intern::from_ref(s.as_ref()))
    }
}

impl std::fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use std::fmt::{Debug, Display};
        match self {
            Self::Bool(b) => Display::fmt(b, f),
            Self::Int(i) => Display::fmt(i, f),
            Self::Uint(u) => Display::fmt(u, f),
            Self::Char(c) => Display::fmt(c, f),
            Self::String(s) => Debug::fmt(s, f),
            Self::Float(fl) => Display::fmt(&fl.0, f),
            Self::Zst(s) => f.write_str(s),
            //Self::Unknown(u) => write!(f, "Unsupported constant: {u}"),
        }
    }
}

impl Allocative for Constant {
    fn visit<'a, 'b: 'a>(&self, visitor: &'a mut allocative::Visitor<'b>) {
        let mut visitor = visitor.enter_self_sized::<Self>();
        if let Self::String(s) = self {
            allocative_visit_intern_t(*s, &mut visitor);
        }
        visitor.exit();
    }
}
