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
///
/// INVARIANT: self.0.len() > 0
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub struct GlobalLocation<'g>(Interned<'g, Vec<GlobalLocationS>>);

impl<'tcx> std::cmp::PartialOrd for GlobalLocation<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
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

impl<'tcx> std::cmp::Ord for GlobalLocation<'tcx> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// Formatting for global locations that works independent of whether it is an
/// interned or inlined location.
pub fn format_global_location<T: IsGlobalLocation>(
    t: &T,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    write_sep(f, "@", t.as_slice().iter().rev(), |elem, f| {
        write!(
            f,
            "{:?}[{}]",
            elem.location.block, elem.location.statement_index
        )
    })?;
    Ok(())
}

impl<'g> std::fmt::Display for GlobalLocation<'g> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        format_global_location(self, f)
    }
}

pub trait IsGlobalLocation: Sized + std::fmt::Display {
    fn outermost(&self) -> GlobalLocationS {
        *self.as_slice().first().unwrap()
    }
    /// Get the `function` field of the underlying location.
    fn outermost_function(&self) -> BodyId {
        self.outermost().function
    }
    /// Get the `location` field of the underlying location.
    fn outermost_location(&self) -> mir::Location {
        self.outermost().location
    }
    /// Get the `next` field of the underlying location.
    fn as_slice(&self) -> &[GlobalLocationS];

    fn innermost(&self) -> GlobalLocationS {
        *self.as_slice().last().unwrap()
    }

    fn innermost_location(&self) -> mir::Location {
        self.innermost().location
    }

    fn innermost_function(&self) -> BodyId {
        self.innermost().function
    }

    /// It this location is top-level (i.e. `self.next() == None`), then return
    /// the `location` field.
    fn as_local(self) -> Option<mir::Location> {
        if self.is_at_root() {
            Some(self.outermost_location())
        } else {
            None
        }
    }
    /// This location is at the top level (e.g. not-nested e.g. `self.next() ==
    /// None`).
    fn is_at_root(&self) -> bool {
        self.as_slice().len() == 1
    }

    fn as_raw(&self) -> RawGlobalLocation {
        RawGlobalLocation(self.as_slice().to_vec())
    }

    /// Create a Forge friendly descriptor for this location as a source of data
    /// in a model flow.
    fn as_data_source<F: FnOnce(mir::Location) -> bool>(
        &self,
        tcx: TyCtxt,
        is_real_location: F,
    ) -> DataSource {
        let GlobalLocationS {
            location: dep_loc,
            function: dep_fun,
        } = self.innermost();
        let is_real_location = is_real_location(dep_loc);
        if self.is_at_root() && !is_real_location {
            DataSource::Argument(self.outermost_location().statement_index - 1)
        } else {
            let terminator = 
                    tcx.body_for_body_id(dep_fun)
                        .simplified_body()
                        .maybe_stmt_at(dep_loc)
                        .unwrap_or_else(|e|
                            panic!("Could not convert {self} to data source with body {}. is at root: {}, is real: {}. Reason: {e:?}", body_name_pls(tcx, dep_fun), self.is_at_root(), is_real_location)
                        )
                        .right()
                        .expect("not a terminator");
            DataSource::FunctionCall(CallSite::new(
                self,
                terminator.as_fn_and_args().unwrap().0,
                tcx,
            ))
        }
    }
}

pub fn iter_parents<L: IsGlobalLocation>(l: &L) -> impl Iterator<Item = &[GlobalLocationS]> {
    let slc = l.as_slice();
    (1..slc.len()).map(|i| &slc[0..i])
}

impl<'g> IsGlobalLocation for GlobalLocation<'g> {
    fn as_slice(&self) -> &[GlobalLocationS] {
        self.0.as_slice()
    }
}

impl<'g> GlobalLocation<'g> {
    /// The naming here might be misleading, this id is *not stable across tool
    /// runs*, but because of the interner it is guaranteed that for any two
    /// locations `g1` and `g2`, `g1.stable_id() == g2.stable_id()` iff `g1 ==
    /// g2`.
    pub fn stable_id(self) -> usize {
        self.0 .0 as *const Vec<GlobalLocationS> as usize
    }

    pub fn to_owned(&self) -> Vec<GlobalLocationS> {
        self.0 .0.clone()
    }

    pub fn parent(self, gli: GLI<'g>) -> Option<Self> {
        if self.is_at_root() {
            None
        } else {
            Some(gli.from_vec(self.as_slice().split_last().unwrap().1.to_vec()))
        }
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
#[derive(PartialEq, Eq, Hash, Debug, Clone, serde::Deserialize, serde::Serialize, Copy)]
pub struct GlobalLocationS {
    /// The id of the body in which this location is located.
    #[serde(with = "crate::serializers::BodyIdProxy")]
    pub function: BodyId,
    /// The location itself
    #[serde(with = "crate::serializers::ser_loc")]
    pub location: mir::Location,
}
/// A serializable non-interned version of [`GlobalLocation`].
///
/// Thanks to the [`IsGlobalLocation`] trait you can use this the same way as a
/// [`GlobalLocation`]. Though be aware that this struct is significantly larger
/// in memory as it contains a singly-linked list of call chains that is not
/// interned.
///
/// For information on the meaning of this struct see [`GlobalLocation`]
#[derive(serde::Deserialize, serde::Serialize, PartialEq, Eq, Hash, Clone, Debug)]
pub struct RawGlobalLocation(Vec<GlobalLocationS>);

impl<'g> From<&'_ GlobalLocation<'g>> for RawGlobalLocation {
    fn from(other: &GlobalLocation<'g>) -> Self {
        (*other).into()
    }
}

impl<'g> From<GlobalLocation<'g>> for RawGlobalLocation {
    fn from(other: GlobalLocation<'g>) -> Self {
        RawGlobalLocation(other.to_owned())
    }
}

impl std::fmt::Display for RawGlobalLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        format_global_location(self, f)
    }
}

impl IsGlobalLocation for RawGlobalLocation {
    fn as_slice(&self) -> &[GlobalLocationS] {
        &self.0
    }
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
    arena: &'g rustc_arena::TypedArena<Vec<GlobalLocationS>>,
    known_locations: ShardedHashMap<&'g Vec<GlobalLocationS>, ()>,
}

impl<'g> GlobalLocationInterner<'g> {
    fn intern_location(&'g self, loc: Vec<GlobalLocationS>) -> GlobalLocation<'g> {
        GlobalLocation(Interned::new_unchecked(
            self.known_locations
                .intern(loc, |loc| self.arena.alloc(loc)),
        ))
    }
    /// Construct a new interner.
    ///
    /// We have to take the arena by reference because the lifetime of the reference ensures it outlives the interner and is not mutated altered.
    pub fn new(arena: &'g rustc_arena::TypedArena<Vec<GlobalLocationS>>) -> Self {
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
        let mut v = vec![GlobalLocationS { function, location }];
        if let Some(others) = next {
            v.extend_from_slice(others.as_slice())
        }
        self.0.intern_location(v)
    }

    pub fn from_vec(self, v: Vec<GlobalLocationS>) -> GlobalLocation<'g> {
        assert!(!v.is_empty());
        self.0.intern_location(v)
    }
    /// Create a top-level [`GlobalLocation`] (e.g. a non-nested call)
    ///
    /// `function` is the id of the [`mir::Body`] that the [`mir::Location`] is from.
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

    pub fn at(self, location: mir::Location, function: BodyId) -> GliAt<'g> {
        GliAt {
            gli: self,
            location,
            function,
        }
    }
}

#[derive(Clone)]
pub struct GliAt<'g> {
    gli: GLI<'g>,
    location: mir::Location,
    function: BodyId,
}

impl<'g> GliAt<'g> {
    pub fn as_global_location(&self) -> GlobalLocation<'g> {
        self.gli.globalize_location(self.location, self.function)
    }
    pub fn relativize(&self, relative: GlobalLocation<'g>) -> GlobalLocation<'g> {
        self.gli
            .global_location_from_relative(relative, self.location, self.function)
    }
}
