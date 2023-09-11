//! Unique identifiers for a point in the MIR program execution that span cross
//! function boundaries.
//!
//! The idea of a global location is to capture the call chain up to a specific
//! location.
//!
//! # Example
//!
//! Consider the following code:
//!
//! ```
//! fn bar() {
//!     let x = 1;
//! }
//!
//! @[dfpp::analyze]
//! fn foo {
//!     bar();
//!     bar();
//! }
//! ```
//!
//! The MIR location of `let x = 1` would likely be something like `bb0[0]` i.e.
//! the 0th statement in basic block 0. However if we construct a flow graph of
//! `foo` that traverses into the called functions (e.g. `bar`), this location
//! is no longer unique. In fact the location of the call to `bar` in `foo`
//! probably also has the MIR location `bb0[0]`. In addition the same function
//! can occur twice so we need to be able to disambiguate a location based on
//! the call chain of getting to the location.
//!
//! So in this example when we inline the first call of `bar` at `bb0[0]` the
//! global location for `let x = 1` for that call is `bb0[0]@bb0[0]` (This is
//! what the `impl Display for GlobalLocation` shows). When the second call is
//! inlined the second `let x = 1` would be `bb0[0]@bb1[0]`.
//!
//! In addition we also capture for every location the `BodyId` of the body the
//! location occurs in, so we can later find the body and the code at that
//! location.
//!
//! # Construction
//!
//! [`GLI::globalize_location`] is used to construct global locations that are
//! not nested in a call chain (such as the location of `let x = 1` within
//! `bar`). A nested location (such as nesting this one behind the call to `bar`
//! in `foo`) is done using [`GLI::global_location_from_relative`].
//!
//! In the example we would first construct global locations for all locations
//! in `bar` with (pseudocode) `bar_bb0[0] = `[`gli.globalize_location(bb0[0],
//! bar_id)`](GLI::globalize_location) and then make the relative locations to
//! foo with [`gli.global_location_from_relative(bar_bb0[0], bb0[0],
//! foo_id)`](GLI::global_location_from_relative) and
//! [`gli.global_location_from_relative(bar_bb0[0], bb1[0],
//! foo_id)`](GLI::global_location_from_relative) for the first and second
//! inlining respectively.
//!
//! # Representation
//!
//! It is organized from the outside in i.e. the top-level function call is the
//! outermost location which calls `next` at `location` going one level deeper
//! and so forth. You may access the innermost location using
//! `GlobalLocation::innermost_location_and_body`.
//!
//! The innermost location is what you'd want to look up if you are wanting to
//! see the actual statement or terminator that this location refers to.
//!
//! # Usage
//!
//! Global locations are intended to be used via the [`IsGlobalLocation`] trait.
//!
//! ## Why we need a trait
//!
//! We intern global locations to make the fact that they are linked lists more
//! efficient. However this makes serialization harder. Since we only use
//! serialization for testing I am doing the lazy thing where I just serialize
//! copies of the linked list. But this also means there's two ways to represent
//! global location, one being the one that recurses with interned pointers, the
//! other uses an owned (e.g. copied) `Box`. This trait lets you treat both of
//! them the same for convenience. This is the reason this trait uses `&self`
//! instead of `self`. For interned values using `self` would be fine, but the
//! serializable version is an owned `Box` and as such would be moved with these
//! function calls.

#[cfg(feature = "rustc")]
use crate::rustc::{hir, mir};
use crate::{rustc_proxies, CallSite, DataSource};
use internment::{Arena, ArenaIntern, Intern};
use serde::{Deserialize, Serialize};
use std::{
    cmp::Ordering,
    fmt::{self, Display},
    ops::Deref,
};

#[cfg(feature = "rustc")]
pub type BodyId = hir::BodyId;
#[cfg(not(feature = "rustc"))]
pub type BodyId = rustc_proxies::BodyId;

#[cfg(feature = "rustc")]
pub type Location = mir::Location;
#[cfg(not(feature = "rustc"))]
pub type Location = rustc_proxies::Location;

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
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy, Serialize, Deserialize)]
pub struct GlobalLocationS {
    #[cfg(feature = "rustc")]
    #[serde(with = "rustc_proxies::BodyId")]
    /// The id of the body in which this location is located.
    pub function: hir::BodyId,
    #[cfg(not(feature = "rustc"))]
    /// The id of the body in which this location is located.
    pub function: rustc_proxies::BodyId,
    #[cfg(feature = "rustc")]
    #[serde(with = "rustc_proxies::Location")]
    /// The location itself
    pub location: mir::Location,
    #[cfg(not(feature = "rustc"))]
    /// The location itself
    pub location: rustc_proxies::Location,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Deserialize, Serialize)]
pub struct RawGlobalLocation(Vec<GlobalLocationS>);

impl RawGlobalLocation {
    /// Get the `next` field of the underlying location.
    pub fn as_slice(&self) -> &[GlobalLocationS] {
        &self.0
    }

    pub fn outermost(&self) -> GlobalLocationS {
        *self.as_slice().first().unwrap()
    }

    /// Get the `function` field of the underlying location.
    pub fn outermost_function(&self) -> BodyId {
        self.outermost().function
    }

    /// Get the `location` field of the underlying location.
    pub fn outermost_location(&self) -> Location {
        self.outermost().location
    }

    pub fn innermost(&self) -> GlobalLocationS {
        *self.as_slice().last().unwrap()
    }

    pub fn innermost_location(&self) -> Location {
        self.innermost().location
    }

    pub fn innermost_function(&self) -> BodyId {
        self.innermost().function
    }

    /// It this location is top-level (i.e. `self.next() == None`), then return
    /// the `location` field.
    pub fn as_local(&self) -> Option<Location> {
        if self.is_at_root() {
            Some(self.outermost_location())
        } else {
            None
        }
    }
    /// This location is at the top level (e.g. not-nested e.g. `self.next() ==
    /// None`).
    pub fn is_at_root(&self) -> bool {
        self.as_slice().len() == 1
    }

    pub fn iter_parents(&self) -> impl Iterator<Item = &[GlobalLocationS]> {
        let slc = self.as_slice();
        (1..slc.len()).map(|i| &slc[0..i])
    }

    pub fn relativize(&self, location: GlobalLocationS) -> Self {
        let mut this = self.clone();
        this.0.insert(0, location);
        this
    }

    pub fn iter(&self) -> impl Iterator<Item = GlobalLocationS> + '_ {
        self.as_slice().iter().copied()
    }
}

impl PartialOrd for RawGlobalLocation {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        for (slf, othr) in self.as_slice().iter().zip(other.as_slice().iter()) {
            if slf.function != othr.function {
                return slf.function.hir_id.partial_cmp(&othr.function.hir_id);
            }
            if slf.location == othr.location {
                return slf.location.partial_cmp(&othr.location);
            }
        }

        self.as_slice().len().partial_cmp(&other.as_slice().len())
    }
}

impl Ord for RawGlobalLocation {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl From<&'_ RawGlobalLocation> for RawGlobalLocation {
    fn from(value: &'_ RawGlobalLocation) -> Self {
        value.clone()
    }
}

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

impl fmt::Display for RawGlobalLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_sep(f, "@", self.as_slice().iter().rev(), |elem, f| {
            write!(
                f,
                "{:?}[{}]",
                elem.location.block, elem.location.statement_index
            )
        })
    }
}

/// The interned version of a global location. See the [module level documentation](super)
/// information on usage and rational.
///
/// To construct these values use [`GLI::globalize_location`] and
/// [`GLI::global_location_from_relative`].
///
/// INVARIANT: self.0.len() > 0
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Clone, Copy, Serialize, Deserialize)]
pub struct GlobalLocation(Intern<RawGlobalLocation>);

impl Deref for GlobalLocation {
    type Target = RawGlobalLocation;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl Display for GlobalLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.as_ref())
    }
}

impl GlobalLocation {
    /// The naming here might be misleading, this id is *not stable across tool
    /// runs*, but because of the interner it is guaranteed that for any two
    /// locations `g1` and `g2`, `g1.stable_id() == g2.stable_id()` iff `g1 ==
    /// g2`.
    pub fn stable_id(self) -> usize {
        self.0.as_ref() as *const RawGlobalLocation as usize
    }

    pub fn to_owned(&self) -> RawGlobalLocation {
        (*self.0).to_owned()
    }

    pub fn parent(self) -> Option<Self> {
        if self.is_at_root() {
            None
        } else {
            let mut this = self.to_owned();
            this.0.pop();
            Some(Self::intern(this))
        }
    }

    pub fn intern(path: RawGlobalLocation) -> Self {
        GlobalLocation(Intern::new(path))
    }

    pub fn intern_ref(path: &RawGlobalLocation) -> Self {
        GlobalLocation(Intern::from_ref(path))
    }

    pub fn single(location: Location, function: BodyId) -> Self {
        Self::intern(RawGlobalLocation(vec![GlobalLocationS {
            location,
            function,
        }]))
    }

    pub fn relativize(&self, location: GlobalLocationS) -> Self {
        Self::intern(self.0.as_ref().relativize(location))
    }
}
