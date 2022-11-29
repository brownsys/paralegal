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

use crate::desc::{CallSite, DataSource, Identifier};
use crate::rust::rustc_arena;
use crate::rust::*;
use crate::utils::*;
use hir::BodyId;
use rustc_data_structures::{intern::Interned, sharded::ShardedHashMap};

/// The interned version of a global location. See the [module level documentation](super)
/// information on usage and rational.
///
/// To construct these values use [`GLI::globalize_location`] and
/// [`GLI::global_location_from_relative`].
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub struct GlobalLocation<'g>(Interned<'g, GlobalLocationS<GlobalLocation<'g>>>);

impl<'tcx> std::cmp::PartialOrd for GlobalLocation<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering;
        if self.function() != other.function() {
            return self.function().hir_id.partial_cmp(&other.function().hir_id);
        }

        if self.location() == other.location() {
            match (self.next(), other.next()) {
                (Some(my_next), Some(other_next)) => my_next.partial_cmp(other_next),
                (None, None) => Some(Ordering::Equal),
                (None, _) => Some(Ordering::Less),
                _ => Some(Ordering::Greater),
            }
        } else {
            self.location().partial_cmp(&other.location())
        }
    }
}

impl<'tcx> std::cmp::Ord for GlobalLocation<'tcx> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

pub trait IsGlobalLocation: Sized {
    /// Every kind of a global location works as a newtype wrapper that feeds
    /// itself as the generic argument to `GlobalLocationS`, the actual payload,
    /// thus closing the type-level recursion. This method takes away that
    /// wrapper layer and lets us operate on the payload.
    fn as_global_location_s(&self) -> &GlobalLocationS<Self>;
    /// Get the `function` field of the underlying location.
    fn function(&self) -> BodyId {
        self.as_global_location_s().function
    }
    /// Get the `location` field of the underlying location.
    fn location(&self) -> mir::Location {
        self.as_global_location_s().location
    }
    /// Get the `next` field of the underlying location.
    fn next(&self) -> Option<&Self> {
        self.as_global_location_s().next.as_ref()
    }
    /// Return the second-to-last location in the chain of `next()` locations.
    /// Returns `None` if this location has no `next()` location.
    fn parent(&self) -> Option<&Self> {
        if let Some(n) = self.next() {
            if n.next().is_none() {
                Some(self)
            } else {
                n.parent()
            }
        } else {
            None
        }
    }
    /// Get the `location` and `function` field of the last location in the
    /// chain of `next()` locations.
    fn innermost_location_and_body(&self) -> (mir::Location, BodyId) {
        self.next().map_or_else(
            || (self.location(), self.function()),
            |other| other.innermost_location_and_body(),
        )
    }
    /// It this location is top-level (i.e. `self.next() == None`), then return
    /// the `location` field.
    fn as_local(self) -> Option<mir::Location> {
        if self.next().is_none() {
            Some(self.location())
        } else {
            None
        }
    }
    /// This location is at the top level (e.g. not-nested e.g. `self.next() ==
    /// None`).
    fn is_at_root(&self) -> bool {
        self.next().is_none()
    }

    /// Create a Forge friendly descriptor for this location as a source of data
    /// in a model flow.
    fn as_data_source<F: FnOnce(mir::Location) -> bool>(
        &self,
        tcx: TyCtxt,
        is_real_location: F,
    ) -> DataSource {
        let (dep_loc, dep_fun) = self.innermost_location_and_body();
        if self.is_at_root() && !is_real_location(dep_loc) {
            DataSource::Argument(self.location().statement_index - 1)
        } else {
            DataSource::FunctionCall(CallSite {
                called_from: Identifier::new(body_name_pls(tcx, dep_fun).name),
                location: dep_loc,
                function: identifier_for_fn(
                    tcx,
                    tcx.body_for_body_id(dep_fun)
                        .body
                        .stmt_at(dep_loc)
                        .right()
                        .expect("not a terminator")
                        .as_fn_and_args()
                        .unwrap()
                        .0,
                ),
            })
        }
    }
}

impl<'g> IsGlobalLocation for GlobalLocation<'g> {
    fn as_global_location_s(&self) -> &GlobalLocationS<Self> {
        self.0 .0
    }
}

impl<'g> GlobalLocation<'g> {
    /// The naming here might be misleading, this id is *not stable across tool
    /// runs*, but because of the interner it is guaranteed that for any two
    /// locations `g1` and `g2`, `g1.stable_id() == g2.stable_id()` iff `g1 ==
    /// g2`.
    pub fn stable_id(self) -> usize {
        self.0 .0 as *const GlobalLocationS<GlobalLocation<'g>> as usize
    }
}

impl<'g> std::borrow::Borrow<GlobalLocationS<GlobalLocation<'g>>> for GlobalLocation<'g> {
    fn borrow(&self) -> &GlobalLocationS<GlobalLocation<'g>> {
        &self.0 .0
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
#[derive(PartialEq, Eq, Hash, Debug, Clone, serde::Deserialize, serde::Serialize)]
pub struct GlobalLocationS<Inner> {
    /// The id of the body in which this location is located.
    #[serde(with = "crate::serializers::BodyIdProxy")]
    pub function: BodyId,
    /// The location itself
    #[serde(with = "crate::serializers::ser_loc")]
    pub location: mir::Location,
    /// If `next.is_some()` then this contains the next link in the call chain.
    /// This means that [`self.location`] refers to a [`mir::Terminator`] and that
    /// this terminator is [`mir::TerminatorKind::Call`]. The next link in the
    /// chain (the payload of the `Some`) is a location in called function.
    pub next: Option<Inner>,
}

/// The interner for `GlobalLocation`s. You should never have to use this
/// directly, use the convenience wrapper type `GLI` instead.
///
/// Be aware that the lifetime of locations is tied to `'g`, meaning you need to
/// allocate the arena before you create the interner. And also the arena must
/// outlive the interner (rustc will make sure to remind you of this).
///
/// Also be aware that interning *will no longer work correctly if you discard
/// the interner*. This is because the decision whether or not to intern a new
/// copy of the location is made using the `known_location` map. If you discard
/// the interner and create a new one its map will be empty. This means it
/// *doesn't know about any previously interned locations* and as a result it
/// will reintern locations, which in turn creates interned values that have the
/// same payload as previously interned locations *and even the same lifetime
/// `'g`*, but have a different pointer value and thus do not compare equal with
/// later interned locations or have the same hash.
pub struct GlobalLocationInterner<'g> {
    arena: &'g rustc_arena::TypedArena<GlobalLocationS<GlobalLocation<'g>>>,
    known_locations: ShardedHashMap<&'g GlobalLocationS<GlobalLocation<'g>>, ()>,
}

impl<'g> GlobalLocationInterner<'g> {
    fn intern_location(&'g self, loc: GlobalLocationS<GlobalLocation<'g>>) -> GlobalLocation<'g> {
        GlobalLocation(Interned::new_unchecked(
            self.known_locations
                .intern(loc, |loc| self.arena.alloc(loc)),
        ))
    }
    /// Construct a new interner.
    ///
    /// We have to take the arena by reference because the lifetime of the reference ensures it outlives the interner and is not mutated altered.
    pub fn new(arena: &'g rustc_arena::TypedArena<GlobalLocationS<GlobalLocation<'g>>>) -> Self {
        GlobalLocationInterner {
            arena,
            known_locations: ShardedHashMap::default(),
        }
    }
}

/// Convenience struct, similar to [`ty::TyCtxt`]. Everything you could ever want
/// from the interner can be done on this struct and it's `Copy` so you don't
/// have to worry about accidentally moving it (as you would when using
/// `&GlobalLocationInterner`).
#[derive(Clone, Copy)]
pub struct GLI<'g>(&'g GlobalLocationInterner<'g>);

impl<'g> GLI<'g> {
    pub fn new(interner: &'g GlobalLocationInterner<'g>) -> Self {
        Self(interner)
    }
    fn make_global_location(
        self,
        function: BodyId,
        location: mir::Location,
        next: Option<GlobalLocation<'g>>,
    ) -> GlobalLocation<'g> {
        self.0.intern_location(GlobalLocationS {
            function,
            location,
            next,
        })
    }
    /// Create a top-level [`GlobalLocation`] (e.g. a non-nested call)
    ///
    /// `function` is the id of the [`mir::Body`] that the [`Location`] is from.
    ///
    /// See the [`IsGlobalLocation`](./trait.IsGlobalLocation.html#construction)
    /// trait for more information.
    pub fn globalize_location(
        self,
        location: mir::Location,
        function: BodyId,
    ) -> GlobalLocation<'g> {
        self.make_global_location(function, location, None)
    }
    /// Make `relative_location` a location in a nested call in `root_function`
    /// at `root_location`
    ///
    /// See the [`IsGlobalLocation`](./trait.IsGlobalLocation.html#construction)
    /// trait for more information.
    pub fn global_location_from_relative(
        self,
        relative_location: GlobalLocation<'g>,
        root_location: mir::Location,
        root_function: BodyId,
    ) -> GlobalLocation<'g> {
        self.make_global_location(root_function, root_location, Some(relative_location))
    }
}
