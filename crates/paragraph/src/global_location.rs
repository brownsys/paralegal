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
//! ```ignore
//! fn bar() {
//!     let x = 1;
//! }
//!
//! #[parable::analyze]
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
//! [`GlobalLocation::single`] is used to construct global locations that are
//! not nested in a call chain (such as the location of `let x = 1` within
//! `bar`). A nested location (such as nesting this one behind the call to `bar`
//! in `foo`) is done using [`GlobalLocation::relativize`].
//!
//! In the example we would first construct global locations for all locations
//! in `bar` with (pseudocode) `bar_bb0[0] = `[`GlobalLocation::single(bb0[0],
//! bar_id)`](GlobalLocation::single) and then make the relative locations to
//! foo with [`bar_bb0[0].relativize(bb0[0], foo_id)`](GlobalLocation::relativize) and
//! [`bar_bb0[0].relativize(bb1[0], foo_id)`](GlobalLocation::relativize) for the first and second
//! inlining respectively.
//!
//! # Representation
//!
//! It is organized from the outside-in, i.e., the top-level function call is the
//! outermost location which calls `next` at `location` going one level deeper
//! and so forth. You may access the innermost location using
//! `GlobalLocation::innermost_location_and_body`.
//!
//! The innermost location is what you'd want to look up if you are wanting to
//! see the actual statement or terminator that this location refers to.

use crate::rustc_proxies;
use internment::Intern;
use serde::{Deserialize, Serialize};
use std::{cmp::Ordering, fmt, ops::Deref};

use crate::rustc_portable::*;

/// The payload type of a global location.
///
/// You will probably want to operate on the interned wrapper type [`GlobalLocation`].
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy, Serialize, Deserialize)]
pub struct GlobalLocationS {
    #[cfg_attr(feature = "rustc", serde(with = "rustc_proxies::BodyId"))]
    /// The id of the body in which this location is located.
    pub function: BodyId,

    #[cfg_attr(feature = "rustc", serde(with = "rustc_proxies::Location"))]
    /// The location itself
    pub location: Location,
}

impl GlobalLocationS {
    pub fn relativize(self, location: GlobalLocation) -> GlobalLocation {
        let mut location = location.to_owned();
        location.0.insert(0, self);
        GlobalLocation::into_intern(location)
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Deserialize, Serialize)]
pub struct RawGlobalLocation(Vec<GlobalLocationS>);

impl RawGlobalLocation {
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

impl fmt::Display for RawGlobalLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::utils::write_sep(f, "@", self.as_slice().iter().rev(), |elem, f| {
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
/// To construct these values use [`GlobalLocation::single`] and
/// [`GlobalLocation::relativize`].
///
/// INVARIANT: `self.0.len() > 0`
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Serialize, Deserialize)]
pub struct GlobalLocation(Intern<RawGlobalLocation>);

impl Deref for GlobalLocation {
    type Target = RawGlobalLocation;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl fmt::Debug for GlobalLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.as_ref().fmt(f)
    }
}

impl fmt::Display for GlobalLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.as_ref().fmt(f)
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
            Some(Self::into_intern(this))
        }
    }

    pub fn into_intern(path: RawGlobalLocation) -> Self {
        GlobalLocation(Intern::new(path))
    }

    pub fn intern(path: &RawGlobalLocation) -> Self {
        GlobalLocation(Intern::from_ref(path))
    }

    pub fn single(location: Location, function: BodyId) -> Self {
        Self::into_intern(RawGlobalLocation(vec![GlobalLocationS {
            location,
            function,
        }]))
    }
}

#[cfg(all(test, not(feature = "rustc")))]
mod test {
    use crate::rustc_proxies::{BasicBlock, DefIndex, HirId, ItemLocalId, LocalDefId, OwnerId};

    use super::*;

    #[test]
    fn test_global_location() {
        let location = Location {
            block: BasicBlock { private: 0 },
            statement_index: 0,
        };

        let function = BodyId {
            hir_id: HirId {
                owner: OwnerId {
                    def_id: LocalDefId {
                        local_def_index: DefIndex { private: 0 },
                    },
                },
                local_id: ItemLocalId { private: 0 },
            },
        };

        let g1 = GlobalLocation::single(location, function);
        let g2 = GlobalLocation::single(location, function);

        // Locations are structurally equal
        assert_eq!(g1, g2);

        // Interning ensures the pointers are the same
        assert_eq!(g1.stable_id(), g2.stable_id());
    }
}
