//! Main analysis pass which proceeds as follows:
//! 
//! 1. The HIR visitor [`CollectingVisitor`](./struct.CollectingVisitor.html)
//!    traverses the HIR and collects annotated entities.
//! 2. [`CollectingVisitor::analyze`](./struct.CollectingVisitor.html#method.analyze)
//!    is called, which initiates a dataflow analysis on every `mir::Body` that
//!    was annotated with `#[dfpp::analyze]` and performs the following steps
//! 
//!    1. Create a
//!       [`GlobalFlowConstructor`](./struct.GlobalFlowConstructor.html)
//!    2. The constructor recursively creates finely granular flow graphs
//!       ([`GlobalFlowGraph`](./struct.GlobalFlowGraph.html)) for callees using
//!       information it gets by running flowistry's dataflow analysis on each
//!       Body. Then it inlines them into the caller using a
//!       [`FunctionInliner`](./struct.FunctionInliner.html) (in
//!       [`compute_granular_global_flow`](./struct.GlobalFlowConstructor.html#method.compute_granular_global_flow))
//!    3. Reduce the inlined, granular graph for the target function to a
//!       `CallOnlyGraph` (on
//!       [`compute_call_only_flow`](./struct.GlobalFlowConstructor.html#method.compute_call_only_flow))
//!    4. Transform the call-only-flow into a
//!       [`desc::Ctrl`](../desc/struct.Ctrl.html) description by adding
//!       information about annotated entities (in
//!       [`CollectingVisitor::handle_target`](./struct.CollectingVisitor.html#method.handle_target))
//! 
//! 3. Combine the [`Ctrl`](../desc/struct.Ctrl.html) graphs into one
//!    [`desc::ProgramDescription`](../desc/struct.ProgramDescription.html)


use std::{
    borrow::{Borrow, Cow},
    cell::RefCell,
    rc::Rc,
};

use crate::{
    dbg::{self, PrintableDependencyMatrix},
    desc::*,
    rust::*,
    sah::HashVerifications,
    utils::*,
    Either, HashMap, HashSet,
};

use hir::{
    def_id::DefId,
    hir_id::HirId,
    intravisit::{self, FnKind},
    BodyId,
};
use mir::{Location, Place, TerminatorKind};
use rustc_data_structures::{intern::Interned, sharded::ShardedHashMap};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    hir::nested_filter::OnlyBodies,
    ty::{self, TyCtxt},
};
use rustc_span::{symbol::Ident, Span, Symbol};

use crate::rust::rustc_arena;
use flowistry::{
    indexed::IndexSet,
    infoflow::{FlowAnalysis, FlowDomain, NonTransitiveFlowDomain},
    mir::{borrowck_facts, engine::AnalysisResults},
};

/// Values of this type can be matched against Rust attributes
pub type AttrMatchT = Vec<Symbol>;

/// A mapping of annotations that are attached to function calls.
///
/// XXX: This needs to be adjusted to attach to the actual call site instead of
/// the function `DefId`
type CallSiteAnnotations = HashMap<DefId, (Vec<Annotation>, usize)>;

/// The result of the data flow analysis for a function.
pub struct Flow<'tcx, 'g> {
    /// The id of the body for which this analysis was requested. The finely
    /// granular (includes statements and non-call terminators), inlined
    /// dataflow analysis for this body can actually be retrieved using
    /// `self.function_flows[self.root_function].unwrap()`
    pub root_function: BodyId,
    /// Memoization of inlined, finely granular (includes statements and
    /// non-call terminators) dataflow analysis result graphs for each function
    /// called directly or indirectly from `self.root_function`.
    function_flows: FunctionFlows<'tcx, 'g>,
    /// The result of removing statements and terminators from the inlined graph
    /// of `self.root_function`. Also uses a representation (input dependencies
    /// vector) that abstracts away the concrete `Place`s the call is performed
    /// with.
    pub reduced_flow: CallOnlyFlow<'g>,
}

/// The idea of a global location is to capture the call chain up to a specific
/// location. The type is organized from the outside in i.e. the top-level
/// function call is the outermost location which calls `next` at `location`
/// going one level deeper and so forth. You may access the innermost location
/// using `GlobalLocation::innermost_location_and_body`.
///
/// The innermost location is what you'd want to look up if you are wanting to
/// see the actual statement or terminator that this location refers to.
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub struct GlobalLocation<'g>(Interned<'g, GlobalLocationS<GlobalLocation<'g>>>);

/// We intern global locations to make the fact that they are linked lists more
/// efficient. However this makes serialization harder. Since we only use
/// serialization for testing I am doing the lazy thing where I just serialize
/// copies of the linked list. But this also means there's two ways to represent
/// global location, one being the one that recurses with interned pointers, the
/// other uses an owned (e.g. copied) `Box`. This trait lets you treat both of
/// them the same for convenience. This is the reason this trait uses `&self`
/// instead of `self`. For interned values using `self` would be fine, but the
/// serializable version is an owned `Box` and as such would be moved with these
/// function calls.
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

/// the naming here might be misleading, this id is *not stable across tool
/// runs*, but because of the interner it is guaranteed that for any two
/// locations `g1` and `g2`, `g1.stable_id() == g2.stable_id()` iff `g1 == g2`.
impl<'g> GlobalLocation<'g> {
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
    pub fn intern_location(
        &'g self,
        loc: GlobalLocationS<GlobalLocation<'g>>,
    ) -> GlobalLocation<'g> {
        GlobalLocation(Interned::new_unchecked(
            self.known_locations
                .intern(loc, |loc| self.arena.alloc(loc)),
        ))
    }
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
    /// Create a top-level [`GlobalLocation`] (e.g. no nested calls).
    pub fn globalize_location(
        self,
        location: mir::Location,
        function: BodyId,
    ) -> GlobalLocation<'g> {
        self.make_global_location(function, location, None)
    }
    /// Make `relative_location` a location in a nested call in `root_function`
    /// at `root_location`
    pub fn global_location_from_relative(
        self,
        relative_location: GlobalLocation<'g>,
        root_location: mir::Location,
        root_function: BodyId,
    ) -> GlobalLocation<'g> {
        self.make_global_location(root_function, root_location, Some(relative_location))
    }
}

/// A flowistry-like dependency matrix at a specific location. Describes for
/// each place the most recent global locations (these could be locations in a
/// callee) that influenced the values at this place.
pub type GlobalDepMatrix<'tcx, 'g> = HashMap<Place<'tcx>, HashSet<GlobalLocation<'g>>>;

/// A flowistry-like 3-dimensional tensor describing the [`Place`] dependencies of
/// all locations (including of inlined callees).
///
/// It is guaranteed that for each place the most recent location that modified
/// it is either
///
/// 1. in the same function (call)
/// 2. one of the argument locations
/// 3. the return or input place of a function call
///
/// In short even with global locations any given place never crosses a function
/// boundary directly but always wither via an argument location or the call
/// site. This is what allow us to use a plain [`Place`], because we can perform
/// translation at these special locations (see also [`translate_child_to_parent`]).
///
/// The special matrix `return_state` is the union of all dependency matrices at
/// each call to `return`.
pub struct GlobalFlowGraph<'tcx, 'g> {
    pub location_states: HashMap<GlobalLocation<'g>, GlobalDepMatrix<'tcx, 'g>>,
    return_state: GlobalDepMatrix<'tcx, 'g>,
}

impl<'tcx, 'g> GlobalFlowGraph<'tcx, 'g> {
    fn new() -> Self {
        GlobalFlowGraph {
            location_states: HashMap::new(),
            return_state: HashMap::new(),
        }
    }
}

/// The analysis result for one function. See [`GlobalFlowGraph`] for
/// explanations, this struct just also bundles in the [`AnalysisResults`] we
/// got from flowistry for the `self.flow.root_function`. Currently the sole
/// purpose of doing this is so that we can later query
/// `self.analysis.analysis.aliases()` to resolve `reachable_values` and
/// [`Place`] [`aliases()`](flowistry::mir::aliases::Aliases::aliases).
struct FunctionFlow<'tcx, 'g> {
    flow: GlobalFlowGraph<'tcx, 'g>,
    analysis: AnalysisResults<'tcx, FlowAnalysis<'tcx, 'tcx, NonTransitiveFlowDomain<'tcx>>>,
}
/// A memoization structure used to memoize and coordinate the recursion in
/// `GlobalFlowConstructor::compute_granular_global_flows`.
type FunctionFlows<'tcx, 'g> = RefCell<HashMap<BodyId, Option<Rc<FunctionFlow<'tcx, 'g>>>>>;
/// Coarse grained, `Place` abstracted version of a `GlobalFlowGraph`.
pub type CallOnlyFlow<'g> = HashMap<GlobalLocation<'g>, CallDeps<GlobalLocation<'g>>>;

/// Dependencies of a function call with the `Place`s abstracted away. Instead
/// each location in the `input_deps` vector corresponds to the dependencies for
/// the positional argument at that index. For methods the 0th index is `self`.
#[derive(serde::Serialize, serde::Deserialize)]
#[serde(bound(
    serialize = "Location: std::cmp::Eq + std::hash::Hash + serde::Serialize",
    deserialize = "Location: std::cmp::Eq + std::hash::Hash + serde::Deserialize<'de>"
))]
pub struct CallDeps<Location> {
    /// Additional dependencies that arise from the control flow, e.g. the scope
    /// this function call is located in.
    pub ctrl_deps: HashSet<Location>,
    /// Dependencies of each argument in the same order as the parameters
    /// provided to the function call.
    pub input_deps: Vec<HashSet<Location>>,
}

/// This function is wholesale lifted from flowistry's recursive analysis. Edits
/// that have been made are just to lift it from a lambda to a top-level
/// function.
///
/// What this function does is relate [`Place`] from the body of a callee to a
/// `Place` in the body of the caller. The most simple example would be one
/// where it relates the formal parameter of a function to the actual call
/// argument as follows. (Shown as MIR)
///
/// ```plain
/// fn callee(_1) {
///   let _2 = ...;
///   ...
/// }
/// fn caller() {
///   ...
///   let _3 = ...;
///   callee(_3)
/// }
/// ```
///
/// Here `translate_child_to_parent(_1) == Some(_3)`. This only works for places
/// that are actually related to the parent, e.g. `translate_child_to_parent(_2)
/// == None` in the example.
///
/// This function does more sophisticated mapping as well through references,
/// derefs and fields. However in all honesty I haven't bothered (yet) to
/// understand its precise capabilities, which should be documented here.
fn translate_child_to_parent<'tcx>(
    tcx: TyCtxt<'tcx>,
    parent_local_def_id: LocalDefId,
    args: &[Option<mir::Place<'tcx>>],
    destination: Option<(mir::Place<'tcx>, mir::BasicBlock)>,
    child: mir::Place<'tcx>,
    mutated: bool,
    body: &mir::Body<'tcx>,
    parent_body: &mir::Body<'tcx>,
) -> Option<mir::Place<'tcx>> {
    use flowistry::mir::utils::PlaceExt;
    use mir::HasLocalDecls;
    use mir::ProjectionElem;
    if child.local == mir::RETURN_PLACE && child.projection.len() == 0 {
        if child.ty(body.local_decls(), tcx).ty.is_unit() {
            return None;
        }

        if let Some((dst, _)) = destination {
            return Some(dst);
        }
    }

    if !child.is_arg(body) || (mutated && !child.is_indirect()) {
        return None;
    }

    // For example, say we're calling f(_5.0) and child = (*_1).1 where
    // .1 is private to parent. Then:
    //    parent_toplevel_arg = _5.0
    //    parent_arg_projected = (*_5.0).1
    //    parent_arg_accessible = (*_5.0)

    let parent_toplevel_arg = args[child.local.as_usize() - 1]?;

    let mut projection = parent_toplevel_arg.projection.to_vec();
    let mut ty = parent_toplevel_arg.ty(parent_body.local_decls(), tcx);
    let parent_param_env = tcx.param_env(parent_local_def_id);
    for elem in child.projection.iter() {
        ty = ty.projection_ty_core(tcx, parent_param_env, &elem, |_, field, _| {
            ty.field_ty(tcx, field)
        });
        let elem = match elem {
            ProjectionElem::Field(field, _) => ProjectionElem::Field(field, ty.ty),
            elem => elem,
        };
        projection.push(elem);
    }

    let parent_arg_projected = Place::make(parent_toplevel_arg.local, &projection, tcx);
    Some(parent_arg_projected)
}

/// Bundles together data needed for the global flow construction. The
/// idea is you construct this with `new` then call
/// `compute_granular_global_flows` and then `compute_call_only_flow` on the
/// result, then discard this struct.
struct GlobalFlowConstructor<'tcx, 'g, 'a, P: InlineSelector + Clone> {
    // Configuration
    /// Command line and environment options that control analysis behavior (for
    /// us and for flowistry).
    analysis_opts: &'a crate::AnalysisCtrl,
    /// Command line and environment options that control debug output.
    dbg_opts: &'a crate::DbgArgs,
    /// A selector that controls which functions are inlined, both in our code
    /// as well as which functions are recursed into in flowistry. See
    /// `InlineSelector` for more information.
    inline_selector: P,

    // Allocators
    /// Rustc query interface
    tcx: TyCtxt<'tcx>,
    /// Global location interner
    gli: GLI<'g>,

    // Memoization
    /// Memoization of intermediate analyses (see `FunctionFlows` documentation for more)
    function_flows: FunctionFlows<'tcx, 'g>,
}

/// This essentially describes a closure that determines for a given
/// `LocalDefId` if it should be inlined. Originally this was in fact done by
/// passing a closure, but it couldn't properly satisfy the type checker,
/// because the selector has to be stored in `fluid_let` variable, which is a
/// dynamically scoped variable. This means that the type needs to be valid for
/// a static lifetime, which I believe closures are not.
///
/// In particular the way that this works is that values of this interface are
/// then wrapped with `RecurseSelector`, which is a flowistry interface that
/// satisfies `flowistry::extensions::RecurseSelector`. The wrapper then simply
/// dispatches to the `InlineSelector`.
///
/// The reason for the two tiers of selectors is that
///
/// - Flowsitry is a separate crate and so I wanted a way to control it that
///   decouples from the specifics of dfpp
/// - We use the selectors to skip functions with annotations, but I wanted to
///   keep the construction of inlined flow graphs agnostic to any notion of
///   annotations. Those are handled by the `Visitor`
///
/// The only implementation currently in use for this is
/// `SkipAnnotatedFunctionSelector`.
pub trait InlineSelector: 'static {
    fn should_inline(&self, tcx: TyCtxt, did: LocalDefId) -> bool;
}

impl<T: InlineSelector> InlineSelector for Rc<T> {
    fn should_inline(&self, tcx: TyCtxt, did: LocalDefId) -> bool {
        self.as_ref().should_inline(tcx, did)
    }
}

/// A `flowistry::extensions::RecurseSelector` that disables recursion if either
///
/// 1. `inline_disabled` has been set (this is usually coming from `crate::AnalysisCtrl::no_recursive_analysis`)
/// 2. The wrapped `InlineSelector` returns `false` for the `LocalDefId` of the called function.
/// 3. The terminator is not a function call
/// 4. The function being called cannot be statically determined
///
/// The last two are incidental and also simultaneously enforced by flowistry.
struct RecurseSelector {
    inline_disabled: bool,
    inline_selector: Box<dyn InlineSelector>,
}

impl flowistry::extensions::RecurseSelector for RecurseSelector {
    fn is_selected<'tcx>(&self, tcx: TyCtxt<'tcx>, tk: &TerminatorKind<'tcx>) -> bool {
        if self.inline_disabled {
            return false;
        }
        if let Ok(fn_and_args) = tk.as_fn_and_args() {
            if let Some(hir::Node::Item(hir::Item { def_id, .. })) =
                tcx.hir().get_if_local(fn_and_args.0)
            {
                return self.inline_selector.should_inline(tcx, *def_id);
            }
        }
        false
    }
}

impl<'tcx, 'g, 'a, P: InlineSelector + Clone> GlobalFlowConstructor<'tcx, 'g, 'a, P> {
    fn new(
        analysis_opts: &'a crate::AnalysisCtrl,
        dbg_opts: &'a crate::DbgArgs,
        tcx: TyCtxt<'tcx>,
        gli: GLI<'g>,
        inline_selector: P,
    ) -> Self {
        Self {
            analysis_opts,
            dbg_opts,
            tcx,
            gli,
            function_flows: RefCell::new(HashMap::new()),
            inline_selector,
        }
    }

    /// This does the same as `RecurseSelector`. It's kind of difficult to reuse
    /// the recurse selector (because it gets moved into a `fluid_let` to
    /// control flowistry recursion), hence this reimplementation here.
    fn should_inline(&self, did: LocalDefId) -> bool {
        !self.analysis_opts.no_recursive_analysis
            && self.inline_selector.should_inline(self.tcx, did)
    }

    /// Find or compute the finely granular flow for the function that this
    /// terminator calls. If successful returns
    ///
    /// 1. The computed flow
    /// 2. The id of the body of the called function
    /// 3. The body of the called function
    /// 4. The arguments to the called function (like `AsFnAndArgs` does).
    /// 5. The return place mentioned in the terminator (like `AsFnAndArgs`
    ///    does)
    ///
    /// This function fails if
    ///
    /// - The terminator is not a function call
    /// - The called function cannot be statically determined (see
    ///   `AsFnAndArgs`)
    /// - The called function is not from the local crate
    /// - `self.should_inline` returned `false` for the defid of the called
    ///   function
    /// - This is a recursive call. Note that this does not only apply for
    ///   direct recursive calls, e.g. `foo` calls `foo`, but also mutual
    ///   recursion e.g. `foo` calls `bar` which calls `foo`.
    ///
    /// The error message will indicate which of these cases occurred.
    fn inner_flow_for_terminator(
        &self,
        t: &mir::Terminator<'tcx>,
    ) -> Result<
        (
            Rc<FunctionFlow<'tcx, 'g>>,
            BodyId,
            &'tcx mir::Body<'tcx>,
            Vec<Option<mir::Place<'tcx>>>,
            Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        ),
        &'static str,
    > {
        t.as_fn_and_args().and_then(|(p, args, dest)| {
            let node = self.tcx.hir().get_if_local(p).ok_or("non-local node")?;
            let (callee_id, callee_local_id, callee_body_id) = node_as_fn(&node)
                .unwrap_or_else(|| panic!("Expected local function node, got {node:?}"));
            let () = if self.should_inline(*callee_local_id) {
                debug!("Selector succeeded for {}.", callee_id.name);
                Ok(())
            } else {
                debug!("Selector failed for {}", callee_id.name);
                Err("Inline selector was false")
            }?;
            let inner_flow = self
                .compute_granular_global_flows(*callee_body_id)
                .ok_or("is recursive")?;
            let body =
                &borrowck_facts::get_body_with_borrowck_facts(self.tcx, *callee_local_id).body;
            debug!("Inner flow for {} computed", callee_id.name);
            Ok((inner_flow, *callee_body_id, body, args, dest))
        })
    }

    /// Computes a granular, inlined flow for the body of the `root_function` id
    /// provided. The granular flow contains all locations in this body,
    /// including those that reference statements and non-call terminators. See
    /// also the documentation for `FunctionFlow`.
    ///
    /// The main work of transforming the body is done by the `FunctionInliner`
    /// struct which, similar to the `GlobalFlowConstructor` bundles together
    /// read-only information and mutable memoization state.
    ///
    /// The computation is memoized in `self.function_flows` and calling this
    /// function will immediately return a previous result, if such a result
    /// exists.
    ///
    /// This function returns `None` if this is a recursive call, e.g. if
    /// `root_function` calls itself somewhere in its call chain. Note that this
    /// means that even if this function is recursive a granular flow *will be
    /// computed*, but only for the outermost call, the recursive call on the
    /// inside will be approximated by its type.
    ///
    /// XXX(Justus): I am actually not sure what the implications of that
    /// approximation are for labels.
    fn compute_granular_global_flows(
        &self,
        root_function: BodyId,
    ) -> Option<Rc<FunctionFlow<'tcx, 'g>>> {
        if let Some(inner) = self.function_flows.borrow().get(&root_function) {
            // `inner` is `Option<...>` here which is deliberate. Not only does this
            // mean that we memoize this expensive inlining computation, but also we
            // avoid recursion. Before we start computing we insert `None` for our
            // own id, and so if a recursion (even a mutual one) occurs it will
            // encounter the `None` and abstract the function instead of inlining
            // it. This might not be the best way to handel recursion though.
            return inner.clone();
        };
        let local_def_id = self.tcx.hir().body_owner_def_id(root_function);

        let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(self.tcx, local_def_id);
        let body = &body_with_facts.body;
        let from_flowistry = {
            use flowistry::extensions::{
                fluid_set, ContextMode, EvalMode, EVAL_MODE, RECURSE_SELECTOR,
            };
            let mut eval_mode = EvalMode::default();
            if !self.analysis_opts.no_recursive_analysis {
                eval_mode.context_mode = ContextMode::Recurse;
            }
            fluid_set!(EVAL_MODE, eval_mode);
            let recurse_selector = Box::new(RecurseSelector {
                inline_disabled: self.analysis_opts.no_recursive_analysis,
                inline_selector: Box::new(self.inline_selector.clone()) as Box<dyn InlineSelector>,
            })
                as Box<dyn flowistry::extensions::RecurseSelector>;
            fluid_set!(RECURSE_SELECTOR, recurse_selector);
            flowistry::infoflow::compute_flow_nontransitive(
                self.tcx,
                root_function,
                body_with_facts,
            )
        };

        // Make sure we terminate on recursion
        self.function_flows.borrow_mut().insert(root_function, None);

        let mut inliner = FunctionInliner {
            from_flowistry: &from_flowistry,
            body,
            local_def_id,
            root_function,
            translated_return_states: RefCell::new(HashMap::new()),
            flow_constructor: self,
            under_construction: Some(GlobalFlowGraph::new()),
        };

        use mir::visit::Visitor;

        inliner.visit_body(&body);

        self.function_flows.borrow_mut().insert(
            root_function,
            Some(Rc::new(FunctionFlow {
                flow: inliner.under_construction.unwrap(),
                analysis: from_flowistry,
            })),
        );
        Some(
            self.function_flows.borrow()[&root_function]
                .as_ref()
                .unwrap()
                .clone(),
        )
    }

    /// Filters the graph `g` for only locations that are function calls while
    /// preserving connections between those locations by flattening transitive
    /// connections via statements between them.
    ///
    /// This is the canonical way for computing a `CallOnlyFlow` and supposed to
    /// be called after/on the result of `compute_granular_global_flows`.
    fn compute_call_only_flow(&self, g: &GlobalFlowGraph<'tcx, 'g>) -> CallOnlyFlow<'g> {
        debug!(
            "Shrinking global flow graph with {} states",
            g.location_states.len()
        );

        let tcx = self.tcx;

        g.location_states
            .iter()
            .filter_map(|(loc, _)| {
                let (inner_location, inner_body) = loc.innermost_location_and_body();
                let (args, _) =
                    Keep::from_location(tcx, inner_body, inner_location, loc.is_at_root())
                        .into_keep()?;
                let flows_borrow = self.function_flows.borrow();

                let ref flow_analysis = flows_borrow
                .get(&inner_body)
                .unwrap()
                .as_ref()
                .unwrap()
                .analysis
                .analysis;

                // Gets the `Aliases` struct for `inner_body` that flowistry has computed for us earlier.
                let ref aliases = flow_analysis.aliases;
                let deep_deps_for =
                    |p: mir::Place<'tcx>| deep_dependencies_of(tcx, aliases, *loc, g, p);

                let ref controlled_by = flow_analysis
                    .control_dependencies
                    .dependent_on(inner_location.block);
                let mut ctrl_deps = HashSet::new();
                for block in controlled_by.into_iter().flat_map(|set| set.iter()) {
                    let mir_location = flow_analysis.body.terminator_loc(block);
                    // Get the terminator location and find all the places that it references, then call deep_deps to find the corresponding dependency locations.
                    let referenced_places = places_read(mir_location, &flow_analysis.body.stmt_at(mir_location));
                    for deps in referenced_places.map(deep_deps_for) {
                        ctrl_deps.extend(deps);
                    }
                }
                Some((
                    *loc,
                    CallDeps {
                        input_deps: args
                            .into_iter()
                            .map(|p| p.map_or_else(|| HashSet::new(), deep_deps_for))
                            .collect(),
                        ctrl_deps: ctrl_deps,
                    },
                ))
            })
            .collect()
    }
}

fn deep_dependencies_of<'tcx, 'g>(
    tcx: TyCtxt<'tcx>,
    aliases: &flowistry::mir::aliases::Aliases<'_, 'tcx>,
    loc: GlobalLocation<'g>,
    g: &GlobalFlowGraph<'tcx, 'g>,
    p: mir::Place<'tcx>,
) -> HashSet<GlobalLocation<'g>> {
    // Get the combined dependencies for `places` at the
    // location `loc` also taking into account provenance.
    let deps_for_places = |loc: GlobalLocation<'g>, places: &[Place<'tcx>]| {
        places
            .iter()
            .flat_map(|place| provenance_of(tcx, *place).into_iter())
            .filter_map(|place| Some((place, g.location_states.get(&loc)?.get(&place)?)))
            .flat_map(|(p, s)| s.iter().map(move |l| (p, *l)))
            .collect::<Vec<(mir::Place<'tcx>, GlobalLocation<'g>)>>()
    };
    let reachable_places = aliases
        .reachable_values(p, ast::Mutability::Not)
        .into_iter()
        .cloned()
        .collect::<Vec<_>>();
    let mut queue = deps_for_places(loc, &reachable_places);
    let mut seen = HashSet::new();
    let mut deps = HashSet::new();

    // A reverse dfs traversing the flowistry tensor which terminates every time we find a function call.
    while let Some((place, location)) = queue.pop() {
        let (local_inner_loc, local_inner_body) = location.innermost_location_and_body();
        match Keep::from_location(
            tcx,
            local_inner_body,
            local_inner_loc,
            location.is_at_root(),
        ) {
            Keep::Keep(..) | Keep::Argument(_) => {
                deps.insert(location);
            }
            Keep::Reject(stmt_at_loc) if !seen.contains(&location) => {
                seen.insert(location);
                queue.extend(deps_for_places(
                    location,
                    &if let Some(stmt) = stmt_at_loc {
                        places_read(location.innermost_location_and_body().0, &stmt)
                            .collect::<Vec<_>>()
                    } else {
                        vec![place]
                    },
                ))
            }
            _ => (),
        }
    }
    deps
}

/// A struct responsible for creating a global flow matrix for one `mir::Body`,
/// inlining all callees (that are configured to be inlined). It is a similar
/// idea to `GlobalFlowConstructor` (in fact it wraps one) that bundles together
/// all information needed to inline into one `mir::Body` so that we can split
/// it into helper functions which all have access to this information.
/// 
/// ## Usage
/// 
/// The function inliner implements `mir::visit::Visitor` that should be applied
/// to only the same `Body` this struct was initialized with.
/// 
/// The methods are currently split into the visit methods that actually modify
/// `self.under_construction` and helper methods such as
/// `self.handle_regular_location` that take an immutable `&self` and return
/// their computed results instead of appending them directly to
/// `under_construction`. This is so that we can use these functions
/// agnostically and later make a determination about where to insert their
/// results. For instance the result of `handle_regular_location` is both
/// inserted into `location_states` but also added to `return_state` when we are
/// handling a terminator. However `handle_regular_location` itself does not
/// know in which context it is being used (to make its implementation simpler).
struct FunctionInliner<'tcx, 'g, 'opts, 'refs, I: InlineSelector + Clone> {
    // Read-only information
    /// The parent constructor struct. For the function we will be inlining we
    /// operate on the flows that this parent has already computed.
    flow_constructor: &'refs GlobalFlowConstructor<'tcx, 'g, 'opts, I>,
    /// A flowistry analysis of `body`
    from_flowistry:
        &'refs AnalysisResults<'tcx, FlowAnalysis<'tcx, 'tcx, NonTransitiveFlowDomain<'tcx>>>,
    /// The source MIR for the body into which we are inlining
    body: &'tcx mir::Body<'tcx>,
    /// The local def id of `body`
    local_def_id: LocalDefId,
    /// The body id of `body`
    root_function: BodyId,

    // Mutable memoization
    /// The return of an inlined function call can be used by several locations.
    /// This map stores the results of translating the callees `Place`s to our
    /// `Place`s for each call site so that we only do that translation once.
    translated_return_states: RefCell<HashMap<mir::Location, GlobalDepMatrix<'tcx, 'g>>>,

    under_construction: Option<GlobalFlowGraph<'tcx, 'g>>,
}

impl<'tcx, 'g, 'opts, 'refs, I: InlineSelector + Clone> FunctionInliner<'tcx, 'g, 'opts, 'refs, I> {
    /// Convenient access to the `TyCtxt`
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.flow_constructor.tcx
    }
    /// Convenient access to the `GLI`
    fn gli(&self) -> GLI<'g> {
        self.flow_constructor.gli
    }

    /// Transform the dependency row for `loc` into one with global locations.
    ///
    /// This is what is done for locations that are non-inlineable calls.
    fn handle_regular_location(&self, loc: mir::Location) -> GlobalDepMatrix<'tcx, 'g> {
        let matrix = self.from_flowistry.state_at(loc).matrix();
        if self.flow_constructor.dbg_opts.dump_flowistry_matrix {
            debug!(
                "Flowistry matrix at {loc:?}\n{}",
                dbg::PrintableMatrix(matrix)
            );
        }
        matrix
            .rows()
            .map(|(place, dep_set)| (place, self.make_row_global(place, dep_set)))
            .collect::<HashMap<_, _>>()
    }

    /// Makes `callee` relative to `call_site` in the function we operate on,
    /// i.e. `self.root_function`
    fn relative_global_location(
        &self,
        call_site: mir::Location,
        callee: GlobalLocation<'g>,
    ) -> GlobalLocation<'g> {
        self.gli()
            .global_location_from_relative(callee, call_site, self.root_function)
    }

    /// Create the state after a callee returns. The main job of this function
    /// is to call `translate_child_to_parent` appropriately on the places
    /// mentioned in the callees dependency matrix at the point of function exit
    /// so that we can query the matrix with the places defined in our function
    /// (i.e. `self.body`)
    fn create_return_state(
        &self,
        l: Location,
        args: &[Option<mir::Place<'tcx>>],
        destination: Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        inner_body: &mir::Body<'tcx>,
        inner_flow: &FunctionFlow<'tcx, 'g>,
    ) -> GlobalDepMatrix<'tcx, 'g> {
        inner_flow
            .flow
            .return_state
            .iter()
            .flat_map(|(&p, deps)| {
                let parent = translate_child_to_parent(
                    self.tcx(),
                    self.local_def_id,
                    &args,
                    destination,
                    p,
                    true,
                    inner_body,
                    self.body,
                );
                let alias_info = &self.from_flowistry.analysis.aliases;
                let aliases = parent
                    .into_iter()
                    .flat_map(|p| alias_info.aliases(p).iter())
                    .collect::<Vec<_>>();
                debug!("  {p:?} -> {aliases:?}");
                aliases.into_iter().map(|&parent| {
                    (
                        parent,
                        deps.iter()
                            .map(|d| {
                                self.gli()
                                    .global_location_from_relative(*d, l, self.root_function)
                            })
                            .collect(),
                    )
                })
            })
            .collect()
    }

    /// Either transforms the location into a global one or, if it names the
    /// boundary of a function call to an inlined function, returns the
    /// translated dependencies of `place`.
    fn globalize_or_inline_call(
        &self,
        place: Place<'tcx>,
        l: Location,
    ) -> impl Iterator<Item = GlobalLocation<'g>> {
        if let Some((t, (inner_flow, body_id, inner_body, args, dest))) =
            if !is_real_location(self.body, l) {
                None
            } else {
                self.body.stmt_at(l)
                    .right()
                    .and_then(|t| Some((t, self.flow_constructor.inner_flow_for_terminator(t).ok()?)))
            }
        {
            debug!("Inspecting inner flow for {:?}", t.kind);
            let mut translated_return_states_borrow =
                self.translated_return_states.borrow_mut();
            // This is ugly but `translate_child_to_parent` only
            // works from the callee to the caller (and I don't want
            // to reimplement/change it right now) so instead I try
            // to translate every possible place in the callee and
            // materialize the result of that in this map, which I
            // memoize in `translated_return_states` so that I only
            // do it once.
            let translated_return_state = translated_return_states_borrow
                .entry(l)
                .or_insert_with(|| {
                    debug!(
                        "Translating return state at location {l:?} in {} with dependency set of size {}, dest is {}",
                        body_name_pls(self.tcx(), body_id).name,
                        inner_flow.flow.return_state.len(),
                        if dest.is_none() { "not " } else { "" }
                    );
                    let return_state = self.create_return_state(l,args.as_slice(), dest, inner_body, inner_flow.borrow());
                    debug!(
                        "  Final state\n{}",
                        PrintableDependencyMatrix::new(&return_state, 4)
                    );
                    return_state
                });
                //let aliases = from_flowistry.analysis.aliases.aliases(place);
            if let Some(deps) = translated_return_state.get(&place) {
                deps.iter().cloned().collect::<Vec<_>>()
            } else {
                warn!(
                    "Dependent place {place:?} not found in translated return states {translated_return_state:?}",
                );
                vec![]
            }
        } else {
            vec![self.gli().make_global_location(self.root_function, l, None)]
        }
        .into_iter()
    }

    fn make_row_global(
        &self,
        place: Place<'tcx>,
        dep_set: IndexSet<mir::Location, flowistry::indexed::RefSet<mir::Location>>,
    ) -> HashSet<GlobalLocation<'g>> {
        dep_set
            .iter()
            .flat_map(|l| self.globalize_or_inline_call(place, *l))
            .collect()
    }
}

impl<'tcx, 'g, 'opts, 'refs, I: InlineSelector + Clone> mir::visit::Visitor<'tcx>
    for FunctionInliner<'tcx, 'g, 'opts, 'refs, I>
{
    fn visit_statement(&mut self, _statement: &mir::Statement<'tcx>, location: Location) {
        let regular_result = self.handle_regular_location(location);
        let global_loc = self
            .gli()
            .make_global_location(self.root_function, location, None);
        self.under_construction
            .as_mut()
            .unwrap()
            .location_states
            .insert(global_loc, regular_result);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        // This lets me use the immutable parts of `self` (as `slf`) when
        // creating the iterators but also mutably modify `under_construction`
        // and `Split` will make sure that `under_construction` gets moved back
        // into `self` at the end.
        let mut splitted: Split<_> = self.into();
        let (ref slf, under_construction) = splitted.as_components();
        if let Ok((inner_flow, inner_body_id, inner_body, args, dest)) =
            slf.flow_constructor.inner_flow_for_terminator(terminator)
        {
            let caller_state = slf.from_flowistry.state_at(location).matrix();
            // Translate every place in the child optimistically
            // to a parent place. This allows us to uphold the
            // invariant that when tracing dependencies a local
            // place does not immediately cross into a parent,
            // but first into such an argument location where it
            // can get translated.
            let as_parent_dep_matrix: GlobalDepMatrix<'tcx, 'g> = inner_flow
                .flow
                .location_states
                .values()
                .flat_map(|s| s.keys())
                .collect::<HashSet<_>>()
                .into_iter()
                .filter_map(|&p| {
                    Some((
                        p,
                        translate_child_to_parent(
                            slf.tcx(),
                            slf.local_def_id,
                            &args,
                            dest,
                            p,
                            false,
                            inner_body,
                            slf.body,
                        )?,
                    ))
                })
                .map(|(child, parent)| {
                    (
                        child,
                        slf.make_row_global(parent, caller_state.row_set(parent)),
                    )
                })
                .collect();

            let locs_to_add = inner_flow
                .flow
                .location_states
                .iter()
                .map(move |(inner_loc, map)| {
                    (
                        slf.relative_global_location(location, *inner_loc),
                        map.iter()
                            .map(|(&place, deps)| {
                                (
                                    place,
                                    deps.iter()
                                        .map(|dep| {
                                            slf.gli().global_location_from_relative(
                                                *dep,
                                                location,
                                                slf.root_function,
                                            )
                                        })
                                        .collect::<HashSet<_>>(),
                                )
                            })
                            .collect::<HashMap<_, _>>(),
                    )
                })
                .chain((1..=args.len()).into_iter().map(move |a| {
                    let global_call_site = slf.gli().globalize_location(
                        mir::Location {
                            block: mir::BasicBlock::from_usize(inner_body.basic_blocks().len()),
                            statement_index: a,
                        },
                        inner_body_id,
                    );
                    let global_arg_loc = slf.relative_global_location(location, global_call_site);
                    (global_arg_loc, as_parent_dep_matrix.clone())
                }));
            under_construction.location_states.extend(locs_to_add);
        } else {
            // First we handle this as the default case. This
            // also recurses as necessary
            let state_at_term = slf.handle_regular_location(location);
            // In the special case of a `return` terminator we
            // merge its state onto any prior state for the
            // return
            if let TerminatorKind::Return = terminator.kind {
                for (p, deps) in state_at_term.iter() {
                    under_construction
                        .return_state
                        .entry(*p)
                        .or_insert_with(|| HashSet::new())
                        .extend(deps.iter().cloned());
                }
            };
            under_construction.location_states.insert(
                slf.gli().globalize_location(location, slf.root_function),
                state_at_term,
            );
        }
    }
}

impl<'tcx, 'g, 'opts, 'refs, I: InlineSelector + Clone> Splittable
    for FunctionInliner<'tcx, 'g, 'opts, 'refs, I>
{
    type Splitted = GlobalFlowGraph<'tcx, 'g>;
    fn split(&mut self) -> Self::Splitted {
        std::mem::replace(&mut self.under_construction, None).unwrap()
    }
    fn merge(&mut self, inner: Self::Splitted) {
        assert!(self.under_construction.is_none());
        self.under_construction = Some(inner)
    }
}

/// A helper struct classifying whether a given `GlobalLocation` should be kept
/// during `compute_call_only_flow`. The main way to use this struct is with the
/// `from_location` function which also has additional documentation.
enum Keep<'tcx> {
    Keep(
        SimplifiedArguments<'tcx>,
        Option<(Place<'tcx>, mir::BasicBlock)>,
    ),
    Argument(usize),
    Reject(Option<Either<&'tcx mir::Statement<'tcx>, &'tcx mir::Terminator<'tcx>>>),
}

impl<'tcx> Keep<'tcx> {
    /// This is an important function that is used multiple times throughout the
    /// dfs later. It is a selector for which locations to keep in the reduced
    /// graph but in addition its variants `Keeps` also transport necessary
    /// information for the search algorithm. This design was chosen because it
    /// allows the use of the same function when we try to figure out whether to
    /// use the location as a sink or a source and also transport some data we
    /// inevitably calculate during that determination.
    fn from_location(
        tcx: TyCtxt<'tcx>,
        body_id: BodyId,
        location: Location,
        loc_is_top_level: bool,
    ) -> Self {
        let body_with_facts =
            borrowck_facts::get_body_with_borrowck_facts(tcx, tcx.hir().body_owner_def_id(body_id));
        if !is_real_location(&body_with_facts.body, location) {
            if loc_is_top_level {
                Keep::Argument(location.statement_index)
            } else {
                Keep::Reject(None)
            }
        } else {
            let stmt_at_loc = body_with_facts.body.stmt_at(location);
            match stmt_at_loc {
                Either::Right(t) => t
                    .as_fn_and_args()
                    .ok()
                    .map_or(Keep::Reject(Some(stmt_at_loc)), |(_, args, dest)| {
                        Keep::Keep(args, dest)
                    }),
                _ => Keep::Reject(Some(stmt_at_loc)),
            }
        }
    }

    /// If this is a `Keep::Keep` variant return its payload, otherwise noting.
    fn into_keep(
        self,
    ) -> Option<(
        SimplifiedArguments<'tcx>,
        Option<(Place<'tcx>, mir::BasicBlock)>,
    )> {
        match self {
            Keep::Keep(args, dest) => Some((args, dest)),
            _ => None,
        }
    }
}

impl<'tcx, 'g> Flow<'tcx, 'g> {
    fn compute<P: InlineSelector + Clone + 'static>(
        opts: &crate::AnalysisCtrl,
        dbg_opts: &crate::DbgArgs,
        tcx: TyCtxt<'tcx>,
        body_id: BodyId,
        gli: GLI<'g>,
        inline_selector: P,
    ) -> Self {
        let mut eval_mode = flowistry::extensions::EvalMode::default();
        if !opts.no_recursive_analysis {
            eval_mode.context_mode = flowistry::extensions::ContextMode::Recurse;
        }
        let constructor = GlobalFlowConstructor::new(opts, dbg_opts, tcx, gli, inline_selector);
        let granular_flow = constructor.compute_granular_global_flows(body_id).unwrap();
        debug!(
            "Granular flow for {}\n{:?}",
            body_name_pls(tcx, body_id).name,
            dbg::PrintableGranularFlow {
                flow: &granular_flow.flow,
                tcx
            }
        );
        let reduced_flow = constructor.compute_call_only_flow(&granular_flow.flow);
        debug!(
            "Constructed reduced flow of {} locations\n{:?}",
            reduced_flow.len(),
            reduced_flow.keys()
        );
        Self {
            root_function: body_id,
            function_flows: constructor.function_flows,
            reduced_flow,
        }
    }
}

/// The only implementation of `InlineSelector` currently in use. This skips
/// inlining for all `LocalDefId` values that are found in the map of
/// `self.marked_objects` i.e. all those functions that have annotations.
#[derive(Clone)]
struct SkipAnnotatedFunctionSelector {
    marked_objects: MarkedObjects,
}

impl InlineSelector for SkipAnnotatedFunctionSelector {
    fn should_inline(&self, tcx: TyCtxt, did: LocalDefId) -> bool {
        self.marked_objects
            .as_ref()
            .borrow()
            .get(&tcx.hir().local_def_id_to_hir_id(did))
            .map_or(true, |anns| anns.0.is_empty())
    }
}

/// A map of objects for which we have found annotations. This is sharable so we
/// can stick it into the `SkipAnnotatedFunctionSelector`. Technically at that
/// point this map is read-only.
type MarkedObjects = Rc<RefCell<HashMap<HirId, (Vec<Annotation>, ObjectType)>>>;

/// This visitor traverses the items in the analyzed crate to discover
/// annotations and analysis targets and store them in this struct. After the
/// discovery phase `self.analyze()` is used to drive the actual analysis. All
/// of this is conveniently encapsulated in the `self.run()` method.
pub struct CollectingVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    opts: &'static crate::Args,
    marked_objects: MarkedObjects,
    marked_stmts: HashMap<HirId, ((Vec<Annotation>, usize), Span, DefId)>,
    functions_to_analyze: Vec<(Ident, BodyId, &'tcx rustc_hir::FnDecl<'tcx>)>,
}

impl<'tcx> CollectingVisitor<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, opts: &'static crate::Args) -> Self {
        Self {
            tcx,
            opts,
            marked_objects: Rc::new(RefCell::new(HashMap::new())),
            marked_stmts: HashMap::new(),
            functions_to_analyze: vec![],
        }
    }

    /// Does the function named by this id have the `dfff::analyze` annotation
    fn should_analyze_function(&self, ident: HirId) -> bool {
        self.tcx
            .hir()
            .attrs(ident)
            .iter()
            .any(|a| a.matches_path(&crate::ANALYZE_MARKER))
    }

    /// Driver function. Performs the data collection via visit, then calls
    /// `self.analyze()` to construct the Forge friendly description of all
    /// endpoints.
    pub fn run(mut self) -> std::io::Result<ProgramDescription> {
        let tcx = self.tcx;
        tcx.hir().deep_visit_all_item_likes(&mut self);
        //println!("{:?}\n{:?}\n{:?}", self.marked_sinks, self.marked_sources, self.functions_to_analyze);
        self.analyze()
    }

    /// Extract all types mentioned in this type for which we have annotations.
    fn annotated_subtypes(&self, ty: ty::Ty) -> HashSet<TypeDescriptor> {
        ty.walk()
            .filter_map(|ty| {
                generic_arg_as_type(ty)
                    .and_then(ty_def)
                    .and_then(DefId::as_local)
                    .and_then(|def| {
                        let hid = self.tcx.hir().local_def_id_to_hir_id(def);
                        if self.marked_objects.as_ref().borrow().contains_key(&hid) {
                            Some(Identifier::new(
                                self.tcx
                                    .item_name(self.tcx.hir().local_def_id(hid).to_def_id()),
                            ))
                        } else {
                            None
                        }
                    })
            })
            .collect()
    }

    /// Perform the analysis for one `#[dfpp::analyze]` annotated function and
    /// return the representation suitable for emitting into Forge.
    fn handle_target<'g>(
        &self,
        _hash_verifications: &mut HashVerifications,
        call_site_annotations: &mut CallSiteAnnotations,
        interesting_fn_defs: &HashMap<DefId, (Vec<Annotation>, usize)>,
        id: Ident,
        b: BodyId,
        gli: GLI<'g>,
    ) -> std::io::Result<(Endpoint, Ctrl)> {
        let mut flows = Ctrl::new();
        let local_def_id = self.tcx.hir().body_owner_def_id(b);
        fn register_call_site<'tcx>(
            tcx: TyCtxt<'tcx>,
            map: &mut CallSiteAnnotations,
            did: DefId,
            ann: Option<&[Annotation]>,
        ) {
            map.entry(did)
                .and_modify(|e| {
                    e.0.extend(ann.iter().flat_map(|a| a.iter()).cloned());
                })
                .or_insert_with(|| {
                    (
                        ann.iter().flat_map(|a| a.iter()).cloned().collect(),
                        tcx.fn_sig(did).skip_binder().inputs().len(),
                    )
                });
        }
        let tcx = self.tcx;
        let controller_body_with_facts =
            borrowck_facts::get_body_with_borrowck_facts(tcx, local_def_id);

        if self.opts.dbg.dump_ctrl_mir {
            mir::graphviz::write_mir_fn_graphviz(
                tcx,
                &controller_body_with_facts.body,
                false,
                &mut outfile_pls(format!("{}.mir.gv", id.name)).unwrap(),
            )
            .unwrap()
        }

        debug!("{}", id.name);
        let flow = Flow::compute(
            &self.opts.anactrl,
            &self.opts.dbg,
            tcx,
            b,
            gli,
            SkipAnnotatedFunctionSelector {
                marked_objects: self.marked_objects.clone(),
            },
        );

        // Register annotations on argument types for this controller.
        let controller_body = &controller_body_with_facts.body;
        {
            let types = controller_body.args_iter().map(|l| {
                let ty = controller_body.local_decls[l].ty;
                let subtypes = self.annotated_subtypes(ty);
                (DataSource::Argument(l.as_usize() - 1), subtypes)
            });
            flows.add_types(types);
        }

        if self.opts.dbg.dump_serialized_non_transitive_graph {
            dbg::write_non_transitive_graph_and_body(
                tcx,
                &flow.reduced_flow,
                outfile_pls(format!("{}.ntgb.json", id.name)).unwrap(),
            );
        }

        if self.opts.dbg.dump_non_transitive_graph {
            outfile_pls(format!("{}.call-only-flow.gv", id.name))
                .and_then(|mut file| {
                    dbg::call_only_flow_dot::dump(tcx, &flow.reduced_flow, &mut file)
                })
                .unwrap_or_else(|err| {
                    error!("Could not write transitive graph dump, reason: {err}")
                })
        }

        for (loc, deps) in flow.reduced_flow.iter() {
            // It's important to look at the innermost location. It's easy to
            // use `location()` and `function()` on a global location instead
            // but that is the outermost call site, not the location for the actual call.
            let (inner_location, inner_body_id) = loc.innermost_location_and_body();
            debug!(
                "Adding dependencies for {:?} in {}",
                inner_location,
                body_name_pls(tcx, inner_body_id).name
            );
            // We need to make sure to fetch the body again here, because we
            // might be looking at an inlined location, so the body we operate
            // on bight not be the `body` we fetched before.
            let inner_body_with_facts = tcx.body_for_body_id(inner_body_id);
            let ref inner_body = inner_body_with_facts.body;
            if !is_real_location(&inner_body, inner_location) {
                assert!(loc.is_at_root());
                // These can only be (controller) arguments and they cannot have
                // dependencies (and thus not receive any data)
                continue;
            }
            let (terminator, (defid, _, _)) = match inner_body
                .stmt_at(inner_location)
                .right()
                .ok_or("not a terminator")
                .and_then(|t| Ok((t, t.as_fn_and_args()?)))
            {
                Ok(term) => term,
                Err(err) => {
                    // We expect to always encounter function calls at this
                    // stage so this could be a hard error, but I made it a
                    // warning because that makes it easier to debug (because
                    // you can see other important down-the-line output that
                    // gives moire information to this error).
                    warn!(
                        "Odd location in graph creation '{}' for {:?}",
                        err,
                        inner_body.stmt_at(inner_location)
                    );
                    continue;
                }
            };
            let call_site = CallSite {
                called_from: Identifier::new(body_name_pls(tcx, inner_body_id).name),
                location: inner_location,
                function: identifier_for_fn(tcx, defid),
            };
            // Propagate annotations on the function object to the call site
            register_call_site(
                tcx,
                call_site_annotations,
                defid,
                interesting_fn_defs.get(&defid).map(|a| a.0.as_slice()),
            );

            let stmt_anns = self.statement_anns_by_loc(defid, terminator);
            let bound_sig = tcx.fn_sig(defid);
            let interesting_output_types: HashSet<_> =
                self.annotated_subtypes(bound_sig.skip_binder().output());
            if !interesting_output_types.is_empty() {
                flows.types.0.insert(
                    DataSource::FunctionCall(call_site.clone()),
                    interesting_output_types,
                );
            }
            if let Some(anns) = stmt_anns {
                // This is currently commented out because hash verification is
                // buggy
                unimplemented!();
                for ann in anns.iter().filter_map(Annotation::as_exception_annotation) {
                    //hash_verifications.handle(ann, tcx, terminator, &body, loc, matrix);
                }
                // TODO this is attaching to functions instead of call
                // sites. Once we start actually tracking call sites
                // this needs to be adjusted
                register_call_site(tcx, call_site_annotations, defid, Some(anns));
            }

            for (arg_slot, arg_deps) in deps.input_deps.iter().enumerate() {
                // This will be the target of any flow we register
                let to = if loc.is_at_root()
                    && matches!(
                        inner_body.stmt_at(loc.location()),
                        Either::Right(mir::Terminator {
                            kind: mir::TerminatorKind::Return,
                            ..
                        })
                    ) {
                    DataSink::Return
                } else {
                    DataSink::Argument {
                        function: call_site.clone(),
                        arg_slot,
                    }
                };
                for dep in arg_deps.iter() {
                    flows.add_data_flow(
                        Cow::Owned(dep.as_data_source(tcx, |l| is_real_location(&inner_body, l))),
                        to.clone(),
                    );
                }
                if self.opts.anactrl.separate_control_deps {
                    for dep in deps.ctrl_deps.iter() {
                        flows.add_ctrl_flow(Cow::Owned(dep.as_data_source(tcx, |l| is_real_location(&inner_body, l))),
                        to.clone(),)
                    }
                } else {
                    for dep in deps.ctrl_deps.iter() {
                        flows.add_data_flow(Cow::Owned(dep.as_data_source(tcx, |l| is_real_location(&inner_body, l))),
                        to.clone(),)
                    }
                }
            }
        }
        Ok((Identifier::new(id.name), flows))
    }

    /// Main analysis driver. Essentially just calls `handle_target` once for
    /// every function in `self.functions_to_analyze` after doing some other
    /// setup necessary for the flow graph creation.
    fn analyze(mut self) -> std::io::Result<ProgramDescription> {
        let arena = rustc_arena::TypedArena::default();
        let interner = GlobalLocationInterner::new(&arena);
        let gli = GLI(&interner);
        let tcx = self.tcx;
        let mut targets = std::mem::replace(&mut self.functions_to_analyze, vec![]);
        let interesting_fn_defs = self
            .marked_objects
            .as_ref()
            .borrow()
            .iter()
            .filter_map(|(s, v)| match v.1 {
                ObjectType::Function(i) => {
                    Some((tcx.hir().local_def_id(*s).to_def_id(), (v.0.clone(), i)))
                }
                _ => None,
            })
            .collect::<HashMap<_, _>>();
        let mut call_site_annotations: CallSiteAnnotations = HashMap::new();
        crate::sah::HashVerifications::with(|hash_verifications| {
            targets
                .drain(..)
                .map(|(id, b, _)| {
                    self.handle_target(
                        hash_verifications,
                        &mut call_site_annotations,
                        &interesting_fn_defs,
                        id,
                        b,
                        gli,
                    )
                })
                .collect::<std::io::Result<HashMap<Endpoint, Ctrl>>>()
                .map(|controllers| ProgramDescription {
                    controllers,
                    annotations: call_site_annotations
                        .into_iter()
                        .map(|(k, v)| (identifier_for_fn(tcx, k), (v.0, ObjectType::Function(v.1))))
                        .chain(
                            self.marked_objects
                                .as_ref()
                                .borrow()
                                .iter()
                                .filter(|kv| kv.1 .1 == ObjectType::Type)
                                .map(|(k, v)| (identifier_for_hid(tcx, *k), v.clone())),
                        )
                        .collect(),
                })
        })
    }

    /// XXX: This selector is somewhat problematic. For one it matches via
    /// source locations, rather than id, and for another we're using `find`
    /// here, which would discard additional matching annotations.
    fn statement_anns_by_loc(&self, p: DefId, t: &mir::Terminator<'tcx>) -> Option<&[Annotation]> {
        self.marked_stmts
            .iter()
            .find(|(_, (_, s, f))| p == *f && s.contains(t.source_info.span))
            .map(|t| t.1 .0 .0.as_slice())
    }
}

fn obj_type_for_stmt_ann(anns: &[Annotation]) -> usize {
    *anns
        .iter()
        .flat_map(|a| match a {
            Annotation::Label(LabelAnnotation { refinement, .. }) => {
                Box::new(refinement.on_argument().iter()) as Box<dyn Iterator<Item = &u16>>
            }
            Annotation::Exception(_) => Box::new(std::iter::once(&0)),
            _ => panic!("Unsupported annotation type for statement annotation"),
        })
        .max()
        .unwrap() as usize
}

impl<'tcx> intravisit::Visitor<'tcx> for CollectingVisitor<'tcx> {
    type NestedFilter = OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    /// Checks for annotations on this id and collects all those id's that have
    /// been annotated.
    fn visit_id(&mut self, id: HirId) {
        let tcx = self.tcx;
        let hir = self.tcx.hir();
        let sink_matches = hir
            .attrs(id)
            .iter()
            .filter_map(|a| {
                a.match_extract(&crate::LABEL_MARKER, |i| {
                    Annotation::Label(crate::ann_parse::ann_match_fn(i))
                })
                .or_else(|| {
                    a.match_extract(&crate::OTYPE_MARKER, |i| {
                        Annotation::OType(crate::ann_parse::otype_ann_match(i))
                    })
                })
                .or_else(|| {
                    a.match_extract(&crate::EXCEPTION_MARKER, |i| {
                        Annotation::Exception(crate::ann_parse::match_exception(i))
                    })
                })
            })
            .collect::<Vec<_>>();
        if !sink_matches.is_empty() {
            let node = self.tcx.hir().find(id).unwrap();
            assert!(if let Some(decl) = node.fn_decl() {
                self.marked_objects
                    .as_ref()
                    .borrow_mut()
                    .insert(id, (sink_matches, ObjectType::Function(decl.inputs.len())))
                    .is_none()
            } else {
                match node {
                    hir::Node::Ty(_)
                    | hir::Node::Item(hir::Item {
                        kind: hir::ItemKind::Struct(..),
                        ..
                    }) => self
                        .marked_objects
                        .as_ref()
                        .borrow_mut()
                        .insert(id, (sink_matches, ObjectType::Type))
                        .is_none(),
                    _ => {
                        let e = match node {
                            hir::Node::Expr(e) => e,
                            hir::Node::Stmt(hir::Stmt { kind, .. }) => match kind {
                                hir::StmtKind::Expr(e) | hir::StmtKind::Semi(e) => e,
                                _ => panic!("Unsupported statement kind"),
                            },
                            _ => panic!("Unsupported object type for annotation {node:?}"),
                        };
                        let obj_type = obj_type_for_stmt_ann(&sink_matches);
                        let did = match e.kind {
                            hir::ExprKind::MethodCall(_, _, _) => {
                                let body_id = hir.enclosing_body_owner(id);
                                let tcres = tcx.typeck(hir.local_def_id(body_id));
                                tcres.type_dependent_def_id(e.hir_id).unwrap_or_else(|| {
                                    panic!("No DefId found for method call {e:?}")
                                })
                            }
                            hir::ExprKind::Call(
                                hir::Expr {
                                    hir_id,
                                    kind: hir::ExprKind::Path(p),
                                    ..
                                },
                                _,
                            ) => {
                                let body_id = hir.enclosing_body_owner(id);
                                let tcres = tcx.typeck(hir.local_def_id(body_id));
                                match tcres.qpath_res(p, *hir_id) {
                                    hir::def::Res::Def(_, did) => did,
                                    res => panic!("Not a function? {res:?}"),
                                }
                            }
                            _ => panic!("Unsupported expression kind {:?}", e.kind),
                        };
                        self.marked_stmts
                            .insert(id, ((sink_matches, obj_type), e.span, did))
                            .is_none()
                    }
                }
            })
        }
    }

    /// Finds the functions that have been marked as targets.
    fn visit_fn(
        &mut self,
        fk: FnKind<'tcx>,
        fd: &'tcx rustc_hir::FnDecl<'tcx>,
        b: BodyId,
        s: Span,
        id: HirId,
    ) {
        match &fk {
            FnKind::ItemFn(ident, _, _) | FnKind::Method(ident, _)
                if self.should_analyze_function(id) =>
            {
                self.functions_to_analyze.push((*ident, b, fd));
            }
            _ => (),
        }

        // dispatch to recursive walk. This is probably unnecessary but if in
        // the future we decide to do something with nested items we may need
        // it.
        intravisit::walk_fn(self, fk, fd, b, s, id)
    }
}
