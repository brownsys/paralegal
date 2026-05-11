//! Utility functions, general purpose structs and extension traits

extern crate smallvec;

use std::{cell::RefCell, collections::hash_map::Entry, hash::Hash, pin::Pin};

use either::Either;
use itertools::Itertools;
use paralegal_pdg::RichLocation;
use thiserror::Error;
use tracing::{info, trace};

use paralegal_rustc_utils::{BodyExt, PlaceExt};

use rustc_ast as ast;
use rustc_borrowck::consumers::PlaceConflictBias;
use rustc_data_structures::{
    fx::{FxHashMap, FxHashSet},
    intern::Interned,
};
use rustc_hir::{
    self as hir, BodyId, Defaultness,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    hir_id::HirId,
};
use rustc_middle::{
    mir::{
        self, Body, ConstOperand, HasLocalDecls, Local, Location, Operand, Place, PlaceElem,
        PlaceRef, PlaceTy, ProjectionElem, Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{
        self, AssocContainer, Binder, EarlyBinder, GenericArg, GenericArgsRef, Instance,
        InstanceKind, Region, Ty, TyCtxt, TyKind, TypeVisitable, TypeVisitor, TypingEnv,
    },
};
use rustc_span::{
    ErrorGuaranteed, Span as RustSpan, Span, Spanned as RustcSpanned, Symbol, symbol::Ident,
};
use rustc_type_ir::{AliasTyKind, PredicatePolarity, RegionKind, TypeFoldable, TypeFolder};

use crate::{
    analysis::is_async_trait_fn, desc::Identifier, mir::FlowistryInput, source_access::BodyCache,
};

pub use paralegal_pdg::{ShortHash, TinyBitSet};

mod print;
pub mod resolve;
mod two_level_cache;

pub use print::*;
pub use two_level_cache::TwoLevelCache;

/// This function exists to deal with `#[tracing::instrument]`. In that case,
/// sadly, the `Span` value attached to a body directly refers only to the
/// `#[tracing::instrument]` macro call. This function instead reconstitutes the
/// span from the collection of spans on each statement.
pub fn body_span<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> RustSpan {
    let source_map = tcx.sess.source_map();
    let body_span = body.span;

    // get me an iterator over the (meaningful) spans in this body. We will use
    // this twice, hence this labmda.
    let mk_span_iter = || {
        body.basic_blocks
            .iter()
            .flat_map(|bbdat| {
                bbdat
                    .statements
                    .iter()
                    .map(|s| s.source_info.span)
                    .chain([bbdat.terminator().source_info.span])
            })
            // If macro try to go to the call
            .map(|s| s.source_callsite())
            // Discard anything not meaningful
            .filter(|s| !s.is_dummy() || !s.is_empty())
    };

    // Probe into the contents of the function. If any span lies within the
    // range of the function span, this is probably not a
    // `#[tracing::instrument]` kind of expantion and we can just use the body span.
    let can_use_body_span = mk_span_iter().all(|sp| sp.from_expansion() || body_span.contains(sp));

    if can_use_body_span {
        return body_span;
    }

    // This is the slow path, where we need to combine multiple spans and check
    // that they are in a reasonable range so we generally avoid this.

    let outer_source_file_idx = source_map.lookup_source_file_idx(body_span.data().lo);

    mk_span_iter()
        // Here we get rid of any spans that don't lie in our source file.
        // Apparently this can happen these days in the macro expansions???
        .filter(|span| {
            let file_idx = source_map.lookup_source_file_idx(span.data().lo);
            file_idx == outer_source_file_idx
        })
        .reduce(RustSpan::to)
        .unwrap_or(body_span)
}

/// If `did` is a method of an `impl` of a trait, then return the `DefId` that
/// refers to the method on the trait definition.
pub fn get_parent(tcx: TyCtxt, did: DefId) -> Option<DefId> {
    matches!(tcx.def_kind(did), DefKind::AssocFn | DefKind::AssocTy)
        .then(|| tcx.associated_item(did).trait_item_def_id())
        .flatten()
}

pub fn is_function_like(tcx: TyCtxt<'_>, did: DefId) -> bool {
    matches!(
        tcx.def_kind(did),
        DefKind::Fn | DefKind::AssocFn | DefKind::Closure
    )
}

pub fn entrypoint_is_async<'tcx>(
    body_cache: &BodyCache<'tcx>,
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> bool {
    tcx.asyncness(def_id).is_async()
        || is_async_trait_fn(tcx, def_id, body_cache.get(def_id).body())
}

/// This is meant as an extension trait for `ast::Attribute`. The main method of
/// interest is [`match_extract`](#tymethod.match_extract),
/// [`matches_path`](#method.matches_path) is interesting if you want to check
/// if this attribute has the path of interest but you do not care about its
/// payload.
pub trait MetaItemMatch {
    /// If the provided symbol path matches the path segments in the attribute
    /// *exactly* then this method applies the parse function and returns the
    /// results of parsing. Otherwise returns `None`.
    ///
    /// In pseudo-rust terms this would mean
    /// ```plain
    /// (#[foo::bar(baz)]   ).match_extract(&sym_vec!["foo", "bar"], |a| a) == Some(baz)
    /// (#[foo(bar)]        ).match_extract(&sym_vec!["foo", "bar"], |a| a) == None
    /// (#[foo::bar::baz(x)]).match_extract(&sym_vec!["foo", "bar"], |a| a) == None
    /// ```
    ///
    /// The [`crate::ann_parse`] module contains a parser combinator framework
    /// suitable for implementing `parse`. For examples on how to run the
    /// functions see the source for
    /// [`match_exception`](crate::ann_parse::match_exception) or
    /// [`ann_match_fn`](crate::ann_parse::ann_match_fn).
    fn match_extract<A, F: Fn(&ast::AttrArgs) -> A>(&self, path: &[Symbol], parse: F) -> Option<A> {
        self.match_get_ref(path).map(parse)
    }
    /// Check that this attribute matches the provided path. All attribute
    /// payload is ignored (i.e. no error if there is a payload).
    fn matches_path(&self, path: &[Symbol]) -> bool {
        self.match_get_ref(path).is_some()
    }

    fn match_get_ref(&self, path: &[Symbol]) -> Option<&ast::AttrArgs>;
}

impl MetaItemMatch for ast::Attribute {
    fn match_get_ref(&self, path: &[Symbol]) -> Option<&ast::AttrArgs> {
        match &self.kind {
            ast::AttrKind::Normal(normal)
                if normal.item.path.segments.len() == path.len()
                    && normal
                        .item
                        .path
                        .segments
                        .iter()
                        .zip(path)
                        .all(|(seg, i)| seg.ident.name == *i) =>
            {
                normal.item.args.unparsed_ref()
            }
            _ => None,
        }
    }
}

/// Extension trait for [`ty::Ty`]. This lets us implement methods on
/// [`ty::Ty`]. [`Self`] is only ever supposed to be instantiated as [`ty::Ty`].
pub trait TyExt: Sized {
    /// Extract a `DefId` if this type references an object that has one. This
    /// is true for most user defined types, including types form the standard
    /// library, but not builtin types, such as `u32`, arrays or ad-hoc types
    /// such as function pointers.
    ///
    /// Use with caution, this function might not be exhaustive (yet).
    fn defid(self) -> Option<DefId> {
        self.defid_ref().copied()
    }
    fn defid_ref(&self) -> Option<&DefId>;
}

impl TyExt for ty::Ty<'_> {
    fn defid_ref(&self) -> Option<&DefId> {
        match self.kind() {
            ty::TyKind::Adt(ty::AdtDef(Interned(ty::AdtDefData { did, .. }, _)), _) => Some(did),
            ty::TyKind::Foreign(did)
            | ty::TyKind::FnDef(did, _)
            | ty::TyKind::Closure(did, _)
            | ty::TyKind::Coroutine(did, _) => Some(did),
            _ => None,
        }
    }
}

pub trait GenericArgExt<'tcx> {
    /// Generic arguments can reference non-type things (in particular constants
    /// and lifetimes). If it is a type, then this extracts that type, otherwise
    /// `None`.
    fn as_type(&self) -> Option<ty::Ty<'tcx>>;
}

impl<'tcx> GenericArgExt<'tcx> for ty::GenericArg<'tcx> {
    fn as_type(&self) -> Option<ty::Ty<'tcx>> {
        match self.kind() {
            ty::GenericArgKind::Type(t) => Some(t),
            _ => None,
        }
    }
}

pub trait DfppBodyExt<'tcx> {
    /// Same as [`mir::Body::stmt_at`] but throws descriptive errors.
    fn stmt_at_better_err(
        &self,
        l: mir::Location,
    ) -> Either<&mir::Statement<'tcx>, &mir::Terminator<'tcx>> {
        self.maybe_stmt_at(l).unwrap()
    }
    /// Non-panicking version of [`mir::Body::stmt_at`] with descriptive errors.
    fn maybe_stmt_at(
        &self,
        l: mir::Location,
    ) -> Result<Either<&mir::Statement<'tcx>, &mir::Terminator<'tcx>>, StmtAtErr<'_, 'tcx>>;
}

#[derive(Debug)]
pub enum StmtAtErr<'a, 'tcx> {
    BasicBlockOutOfBound(mir::BasicBlock, &'a mir::Body<'tcx>),
    StatementIndexOutOfBounds(usize, &'a mir::BasicBlockData<'tcx>),
}

impl<'tcx> DfppBodyExt<'tcx> for mir::Body<'tcx> {
    fn maybe_stmt_at(
        &self,
        l: mir::Location,
    ) -> Result<Either<&mir::Statement<'tcx>, &mir::Terminator<'tcx>>, StmtAtErr<'_, 'tcx>> {
        let Location {
            block,
            statement_index,
        } = l;
        let block_data = self
            .basic_blocks
            .get(block)
            .ok_or(StmtAtErr::BasicBlockOutOfBound(block, self))?;
        if statement_index == block_data.statements.len() {
            Ok(Either::Right(block_data.terminator()))
        } else if let Some(stmt) = block_data.statements.get(statement_index) {
            Ok(Either::Left(stmt))
        } else {
            Err(StmtAtErr::StatementIndexOutOfBounds(
                statement_index,
                block_data,
            ))
        }
    }
}

pub trait InstanceExt<'tcx> {
    /// Get the most precise type signature we can for this function, erase any
    /// regions and discharge binders.
    ///
    /// Returns an error if it was impossible to get any signature.
    ///
    /// Emits warnings if a precise signature could not be obtained or there
    /// were type variables not instantiated.
    fn sig(self, tcx: TyCtxt<'tcx>) -> Result<ty::FnSig<'tcx>, ErrorGuaranteed>;
}

impl<'tcx> InstanceExt<'tcx> for Instance<'tcx> {
    fn sig(self, tcx: TyCtxt<'tcx>) -> Result<ty::FnSig<'tcx>, ErrorGuaranteed> {
        let def_id = self.def_id();
        let fn_kind = FunctionKind::for_def_id(tcx, def_id)?;
        let typing_env = TypingEnv::fully_monomorphized();
        let late_bound_sig = match fn_kind {
            FunctionKind::Generator => self.ty(tcx, typing_env).fn_sig(tcx),
            FunctionKind::Closure => self.args.as_closure().sig(),
            FunctionKind::Plain => self.ty(tcx, typing_env).fn_sig(tcx),
        };
        Ok(tcx.normalize_erasing_late_bound_regions(typing_env, late_bound_sig))
    }
}

/// This exists to distinguish different types of functions, which is necessary
/// because depending on the type of function, the method of requesting its
/// signature from `TyCtxt` differs.
///
/// In addition generators also return true for `TyCtxt::is_closure` but must
/// request their signature differently. Thus we factor that determination out
/// into this enum.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum FunctionKind {
    Closure,
    Generator,
    Plain,
}

impl FunctionKind {
    pub fn for_def_id(tcx: TyCtxt, def_id: DefId) -> Result<Self, ErrorGuaranteed> {
        if tcx.coroutine_kind(def_id).is_some() {
            Ok(Self::Generator)
        } else if tcx.is_closure_like(def_id) {
            Ok(Self::Closure)
        } else if tcx.def_kind(def_id).is_fn_like() {
            Ok(Self::Plain)
        } else {
            Err(tcx
                .dcx()
                .span_err(tcx.def_span(def_id), "Expected this item to be a function."))
        }
    }
}

pub fn func_of_term<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &Terminator<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let mir::TerminatorKind::Call { func, .. } = &terminator.kind else {
        return None;
    };
    let const_ = func.constant()?;
    let ty = ty_of_const(const_);
    type_as_fn(tcx, ty).to_option()
}

/// A simplified version of the argument list that is stored in a
/// `TerminatorKind::Call`.
///
/// The vector contains `None` in those places where the function is called with
/// a constant. This means it is guaranteed to be as long as the list of formal
/// parameters of this function, which in turn means it can be zipped up with
/// e.g. the types of the arguments of the function definition
pub type SimplifiedArguments<'tcx> = Vec<Option<Place<'tcx>>>;

/// Extension trait for function calls (e.g. `mir::TerminatorKind` and
/// `mir::Terminator`) that lets you decompose the call into a convenient
/// (function definition, arguments, return place) tuple *in such cases when*
///
/// a. The terminator is a function call (i.e. `mir::TerminatorKind::Call`)
/// b. The callee can be statically determined (i.e. not an opaque function
///    pointer).
///
/// The error message conveys which of these assumptions failed.
///
/// The argument vector contains `None` in those places where the function is
/// called with a constant. This means it is guaranteed to be as long as the
/// list of formal parameters of this function, which in turn means it can be
/// zipped up with e.g. the types of the arguments of the function definition
pub trait AsFnAndArgs<'tcx> {
    fn as_fn_and_args(
        &self,
        tcx: TyCtxt<'tcx>,
    ) -> Result<(DefId, SimplifiedArguments<'tcx>, mir::Place<'tcx>), AsFnAndArgsErr<'tcx>> {
        self.as_instance_and_args(tcx)
            .map(|(inst, args, ret)| (inst.def_id(), args, ret))
    }

    fn as_instance_and_args(
        &self,
        tcx: TyCtxt<'tcx>,
    ) -> Result<(Instance<'tcx>, SimplifiedArguments<'tcx>, mir::Place<'tcx>), AsFnAndArgsErr<'tcx>>;
}

#[derive(Debug, Error)]
pub enum AsFnAndArgsErr<'tcx> {
    #[error("not a constant")]
    NotAConstant,
    #[error("is not a function type: {0:?}")]
    NotFunctionType(ty::TyKind<'tcx>),
    #[error("is not a `Val` constant: {0}")]
    NotValueLevelConstant(ty::Const<'tcx>),
    #[error("terminator is not a `Call`")]
    NotAFunctionCall,
    #[error("function instance resolution errored")]
    InstanceResolutionErr,
    #[error("could not normalize generics {0}")]
    NormalizationError(String),
    #[error("instance too unspecific")]
    InstanceTooUnspecific,
}

pub fn ty_of_const<'tcx>(c: &ConstOperand<'tcx>) -> Ty<'tcx> {
    match c.const_ {
        mir::Const::Val(_, ty) => ty,
        mir::Const::Ty(cst, _) => cst,
        mir::Const::Unevaluated { .. } => unreachable!(),
    }
}

impl<'tcx> AsFnAndArgs<'tcx> for mir::Terminator<'tcx> {
    fn as_instance_and_args(
        &self,
        tcx: TyCtxt<'tcx>,
    ) -> Result<(Instance<'tcx>, SimplifiedArguments<'tcx>, mir::Place<'tcx>), AsFnAndArgsErr<'tcx>>
    {
        let mir::TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &self.kind
        else {
            return Err(AsFnAndArgsErr::NotAFunctionCall);
        };
        let ty = ty_of_const(func.constant().ok_or(AsFnAndArgsErr::NotAConstant)?);
        let Some((def_id, gargs)) = type_as_fn(tcx, ty).to_option() else {
            return Err(AsFnAndArgsErr::NotFunctionType(*ty.kind()));
        };
        test_generics_normalization(tcx, gargs)
            .map_err(|e| AsFnAndArgsErr::NormalizationError(format!("{e:?}")))?;
        let instance =
            ty::Instance::try_resolve(tcx, TypingEnv::fully_monomorphized(), def_id, gargs)
                .map_err(|_| AsFnAndArgsErr::InstanceResolutionErr)?
                .ok_or(AsFnAndArgsErr::InstanceTooUnspecific)?;
        Ok((
            instance,
            args.iter().map(|a| a.node.place()).collect(),
            *destination,
        ))
    }
}

/// Try and normalize the provided generics.
///
/// The purpose of this function is to test whether resolving these generics
/// will return an error. We need this because [`ty::Instance::resolve`] fails
/// with a hard error when this normalization fails (even though it returns
/// [`Result`]). However legitimate situations can arise in the code where this
/// normalization fails for which we want to report warnings but carry on with
/// the analysis which a hard error doesn't allow us to do.
fn test_generics_normalization<'tcx>(
    tcx: TyCtxt<'tcx>,
    args: &'tcx ty::List<ty::GenericArg<'tcx>>,
) -> Result<(), ty::normalize_erasing_regions::NormalizationError<'tcx>> {
    tcx.try_normalize_erasing_regions(
        TypingEnv::fully_monomorphized(),
        ty::Unnormalized::new(args),
    )
    .map(|_| ())
}

/// A struct that can be used to apply a `FnMut` to every `Place` in a MIR
/// object via the `visit::Visitor` trait. Usually used to accumulate information
/// about the places.
pub struct PlaceVisitor<F>(pub F);

impl<'tcx, F: FnMut(&mir::Place<'tcx>)> mir::visit::Visitor<'tcx> for PlaceVisitor<F> {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) {
        self.0(place)
    }
}

/// Extension trait for [`hir::Node`]. This lets up implement methods on
/// [`hir::Node`]. [`Self`] should only ever be instantiated as [`hir::Node`].
pub trait NodeExt<'hir> {
    /// Try and unwrap this `node` as some sort of function.
    ///
    /// [HIR](hir) has two different kinds of items that are types of function,
    /// one is top-level `fn`s the other is an `impl` item of function type.
    /// This function lets you extract common information from either. Returns
    /// [`None`] if the node is not of a function-like type.
    fn as_fn(&self, tcx: TyCtxt) -> Option<(Ident, hir::def_id::LocalDefId, BodyId)>;
}

impl<'hir> NodeExt<'hir> for hir::Node<'hir> {
    fn as_fn(&self, tcx: TyCtxt) -> Option<(Ident, hir::def_id::LocalDefId, BodyId)> {
        match self {
            hir::Node::Item(hir::Item {
                owner_id,
                kind:
                    hir::ItemKind::Fn {
                        ident,
                        body: body_id,
                        ..
                    },
                ..
            })
            | hir::Node::ImplItem(hir::ImplItem {
                ident,
                owner_id,
                kind: hir::ImplItemKind::Fn(_, body_id),
                ..
            }) => Some((*ident, owner_id.def_id, *body_id)),
            hir::Node::Expr(hir::Expr {
                kind: hir::ExprKind::Closure(hir::Closure { body: body_id, .. }),
                ..
            }) => Some((
                Ident::from_str("closure"),
                tcx.hir_body_owner_def_id(*body_id),
                *body_id,
            )),
            _ => None,
        }
    }
}

/// A trait for types that can be converted into a [`mir::LocalDefId`] via
/// [`TyCtxt`].
pub trait IntoLocalDefId {
    fn into_local_def_id(self, tcx: TyCtxt) -> LocalDefId;
}

impl IntoLocalDefId for LocalDefId {
    #[inline]
    fn into_local_def_id(self, _tcx: TyCtxt) -> LocalDefId {
        self
    }
}

impl IntoLocalDefId for BodyId {
    #[inline]
    fn into_local_def_id(self, tcx: TyCtxt) -> LocalDefId {
        tcx.hir_body_owner_def_id(self)
    }
}

impl IntoLocalDefId for HirId {
    #[inline]
    fn into_local_def_id(self, _: TyCtxt) -> LocalDefId {
        self.expect_owner().def_id
    }
}

impl<D: Copy + IntoLocalDefId> IntoLocalDefId for &'_ D {
    #[inline]
    fn into_local_def_id(self, tcx: TyCtxt) -> LocalDefId {
        (*self).into_local_def_id(tcx)
    }
}

pub trait ProjectionElemExt {
    fn may_be_indirect(self) -> bool;
}

impl<V, T> ProjectionElemExt for ProjectionElem<V, T> {
    fn may_be_indirect(self) -> bool {
        matches!(
            self,
            ProjectionElem::Field(..)
                | ProjectionElem::Index(..)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. }
        )
    }
}

/// Brother to [`IntoLocalDefId`], converts the id type to a [`DefId`] using [`TyCtxt`]
pub trait IntoDefId {
    fn into_def_id(self, tcx: TyCtxt) -> DefId;
}

impl IntoDefId for DefId {
    #[inline]
    fn into_def_id(self, _: TyCtxt) -> DefId {
        self
    }
}

impl IntoDefId for LocalDefId {
    #[inline]
    fn into_def_id(self, _: TyCtxt) -> DefId {
        self.to_def_id()
    }
}

impl IntoDefId for HirId {
    #[inline]
    fn into_def_id(self, tcx: TyCtxt) -> DefId {
        self.into_local_def_id(tcx).to_def_id()
    }
}

impl<D: Copy + IntoDefId> IntoDefId for &'_ D {
    #[inline]
    fn into_def_id(self, tcx: TyCtxt) -> DefId {
        (*self).into_def_id(tcx)
    }
}

impl IntoDefId for BodyId {
    #[inline]
    fn into_def_id(self, tcx: TyCtxt) -> DefId {
        tcx.hir_body_owner_def_id(self).into_def_id(tcx)
    }
}

impl IntoDefId for Res {
    #[inline]
    fn into_def_id(self, _: TyCtxt) -> DefId {
        match self {
            Res::Def(_, did) => did,
            _ => panic!("turning non-def res into DefId; res is: {:?}", self),
        }
    }
}

/// Get a reasonable, but not guaranteed unique name for this item
pub fn identifier_for_item(tcx: TyCtxt, did: DefId) -> Identifier {
    // TODO Make a generic version instead of just copying `unique_identifier_for_item`
    let get_parent = || identifier_for_item(tcx, tcx.parent(did));
    Identifier::new_intern(
        &tcx.opt_item_name(did)
            .map(|n| n.to_string())
            .or_else(|| {
                use hir::def::DefKind::*;
                match tcx.def_kind(did) {
                    OpaqueTy => Some("Opaque".to_string()),
                    Closure => {
                        let suffix = if tcx.is_coroutine(did) {
                            "coroutine"
                        } else {
                            "closure"
                        };
                        Some(format!("{}_{}", get_parent(), suffix))
                    }
                    _ => None,
                }
            })
            .unwrap_or_else(|| {
                panic!(
                    "Could not name {} {:?}",
                    tcx.def_path_debug_str(did),
                    tcx.def_kind(did)
                )
            }),
    )
}

/// Conveniently create a vector of [`Symbol`]s. This way you can just write
/// `sym_vec!["s1", "s2", ...]` and this macro will make sure to call
/// [`Symbol::intern`]
#[macro_export]
macro_rules! sym_vec {
    ($($e:expr),*) => {
        vec![$(rustc_span::Symbol::intern($e)),*]
    };
}

pub fn time<R, F: FnOnce() -> R>(msg: &str, f: F) -> R {
    info!("Starting {msg}");
    let time = std::time::Instant::now();
    let r = f();
    info!("{msg} took {}", humantime::format_duration(time.elapsed()));
    r
}

pub trait Spanned<'tcx> {
    fn span(&self, tcx: TyCtxt<'tcx>) -> Span;
}

impl<'tcx> Spanned<'tcx> for mir::Terminator<'tcx> {
    fn span(&self, _tcx: TyCtxt<'tcx>) -> Span {
        self.source_info.span
    }
}

impl<'tcx> Spanned<'tcx> for mir::Statement<'tcx> {
    fn span(&self, _tcx: TyCtxt<'tcx>) -> Span {
        self.source_info.span
    }
}

impl<'tcx> Spanned<'tcx> for (&mir::Body<'tcx>, mir::Location) {
    fn span(&self, tcx: TyCtxt<'tcx>) -> Span {
        self.0
            .stmt_at(self.1)
            .either(|e| e.span(tcx), |e| e.span(tcx))
    }
}

impl<'tcx> Spanned<'tcx> for (&mir::Body<'tcx>, RichLocation) {
    fn span(&self, tcx: TyCtxt<'tcx>) -> RustSpan {
        let (body, loc) = self;
        match loc {
            RichLocation::Location(loc) => (*body, *loc).span(tcx),
            RichLocation::End | RichLocation::Start => body.span,
        }
    }
}

impl<'tcx> Spanned<'tcx> for DefId {
    fn span(&self, tcx: TyCtxt<'tcx>) -> Span {
        tcx.def_span(*self)
    }
}

pub fn map_either<A, B, C, D>(
    either: Either<A, B>,
    f: impl FnOnce(A) -> C,
    g: impl FnOnce(B) -> D,
) -> Either<C, D> {
    match either {
        Either::Left(l) => Either::Left(f(l)),
        Either::Right(r) => Either::Right(g(r)),
    }
}

pub fn type_for_constructor(tcx: TyCtxt, def_id: DefId) -> DefId {
    assert!(tcx.is_constructor(def_id));
    let parent = tcx.parent(def_id);
    match tcx.def_kind(parent) {
        DefKind::Variant => {
            let ty = tcx.parent(parent);
            assert_eq!(tcx.def_kind(ty), DefKind::Enum);
            ty
        }
        DefKind::Struct => parent,
        other => {
            panic!("Expected a variant or struct, got {other:?}");
        }
    }
}

#[derive(Default)]
/// A lazily filled contiguous cache of values indexed by integers.
pub struct ContiguousIntCache<T>(RefCell<Vec<Pin<Box<T>>>>);

impl<T> ContiguousIntCache<T> {
    pub fn new() -> Self {
        Self(RefCell::new(Vec::new()))
    }

    /// Returns a reference corresponding to the given index key. Note that, if
    /// the index is not yet found in the cache, it and all values with lower
    /// indices are created and inserted. As such the initialization function
    /// `f` is called for each missing index and must support creating all of
    /// these values.
    pub fn get_or_insert<'s>(&'s self, index: usize, f: impl Fn(usize) -> T) -> &'s T {
        {
            let mut m = self.0.borrow_mut();
            let mut i = m.len();
            if index >= m.len() {
                m.resize_with(index + 1, || {
                    let v = Box::pin(f(i));
                    i += 1;
                    v
                });
            }
        }
        unsafe { std::mem::transmute::<&'_ T, &'s T>(&*self.0.borrow()[index]) }
    }

    pub fn try_get<'s>(&'s self, index: usize) -> Option<&'s T> {
        unsafe {
            std::mem::transmute::<Option<&'_ T>, Option<&'s T>>(
                self.0.borrow().get(index).map(|v| &**v),
            )
        }
    }
}

pub fn flatten_child_items(
    tcx: ty::TyCtxt,
    modules: impl IntoIterator<Item = DefId>,
) -> FxHashSet<DefId> {
    use rustc_hir::def::DefKind;
    let mut queue: Vec<_> = modules.into_iter().collect();
    trace!("flatten_child_items starting with: {:?}", queue);
    let mut seen = FxHashSet::default();
    seen.extend(queue.iter().cloned());
    let mut result = FxHashSet::default();

    while let Some(module) = queue.pop() {
        let def_kind = tcx.def_kind(module);
        trace!(
            "Processing item: {} with def kind {:?}",
            tcx.def_path_str(module),
            def_kind
        );
        let children = match def_kind {
            DefKind::Mod => {
                let it = if let Some(local) = module.as_local() {
                    tcx.module_children_local(local)
                } else {
                    tcx.module_children(module)
                }
                .iter()
                .filter_map(|c| c.res.opt_def_id())
                // Only follow items directly defined in this module, not
                // re-exports. Re-exported items have their defining module as
                // parent, not this one, so they should not inherit its markers.
                .filter(|c| {
                    let parent = tcx.opt_parent(*c);
                    assert!(
                        parent.is_some() || c.is_crate_root(),
                        "{c:?} has no parent but isn't a crate (is {:?})",
                        tcx.def_kind(*c)
                    );
                    parent.is_some_and(|parent| parent == module)
                })
                .chain(
                    // Trait impls are not contained in `module_children` where
                    // they are defined, but instead associated with the crate
                    // itself.
                    module
                        .as_crate_root()
                        .map(|c| tcx.trait_impls_in_crate(c))
                        .into_iter()
                        .flatten()
                        .copied(),
                );
                Box::new(it) as Box<dyn Iterator<Item = DefId>>
            }
            DefKind::Impl { .. } => Box::new(
                tcx.associated_items(module)
                    .in_definition_order()
                    .map(|i| i.def_id),
            ) as Box<_>,
            DefKind::Struct | DefKind::Enum => {
                Box::new(tcx.inherent_impls(module).iter().copied()) as Box<_>
            }
            _ => {
                continue;
            }
        };
        for id in children {
            let def_kind = tcx.def_kind(id);
            trace!(
                "Processing child item: {} with def kind {:?}",
                tcx.def_path_str(id),
                def_kind
            );
            match def_kind {
                DefKind::Struct | DefKind::Enum | DefKind::Mod | DefKind::Impl { .. }
                    if !seen.contains(&id) =>
                {
                    seen.insert(id);
                    queue.push(id);
                }
                DefKind::Fn | DefKind::AssocFn | DefKind::Closure => {
                    result.insert(id);
                }
                _ => {}
            }
        }
    }

    result
}
/// An async check that does not crash if called on closures.
pub fn is_async(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    !tcx.is_closure_like(def_id) && !tcx.is_constructor(def_id) && tcx.asyncness(def_id).is_async()
}

pub type ArgSlice<'a, 'tcx> = &'a [RustcSpanned<Operand<'tcx>>];

/// Resolve the `def_id` item to an instance.
pub fn try_resolve_function<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    typing_env: TypingEnv<'tcx>,
    args: GenericArgsRef<'tcx>,
) -> Option<Instance<'tcx>> {
    let typing_env = typing_env.with_post_analysis_normalized(tcx);
    Instance::try_resolve(tcx, typing_env, def_id, args).unwrap()
}

pub fn place_ty_eq<'tcx>(a: PlaceTy<'tcx>, b: PlaceTy<'tcx>) -> bool {
    a.ty == b.ty && a.variant_index == b.variant_index
}

/// Returns whether this method is expected to have a body we can analyze.
///
/// Specifically this returns `true` if `function` refers to an associated item
/// of a trait which has *no* default value.
///
/// Note: While you are supposed to call this with a `function` that refers to a
/// function, it will not crash if it refers to a type or constant instead.
pub fn is_virtual(tcx: TyCtxt, function: DefId) -> bool {
    tcx.opt_associated_item(function).is_some_and(|assoc_item| {
        matches!(
            assoc_item.container,
            AssocContainer::Trait
            if !matches!(
                assoc_item.defaultness(tcx),
                Defaultness::Default { has_value: true })
        )
    })
}

pub fn erase_regions<'tcx, T>(tcx: TyCtxt<'tcx>, t: T) -> T
where
    T: TypeFoldable<TyCtxt<'tcx>> + std::fmt::Debug,
{
    struct VarEraser<'tcx> {
        tcx: TyCtxt<'tcx>,
    }

    impl<'tcx> TypeFolder<TyCtxt<'tcx>> for VarEraser<'tcx> {
        fn cx(&self) -> TyCtxt<'tcx> {
            self.tcx
        }

        fn fold_region(&mut self, mut r: Region<'tcx>) -> Region<'tcx> {
            if r.is_var() {
                r = Region::new_from_kind(self.tcx, RegionKind::ReErased)
            }
            r
        }
    }

    let mut eraser = VarEraser { tcx };
    t.fold_with(&mut eraser)
}

/// The "canonical" way we monomorphize
pub fn try_monomorphize<'tcx, 'a, T>(
    inst: Instance<'tcx>,
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    t: T,
    span: Span,
) -> Result<T, ErrorGuaranteed>
where
    T: TypeFoldable<TyCtxt<'tcx>> + std::fmt::Debug,
{
    let t = erase_regions(tcx, t);

    inst.try_instantiate_mir_and_normalize_erasing_regions(tcx, typing_env, EarlyBinder::bind(t))
        .map_err(|e| {
            tcx.dcx().span_err(
                span,
                format!("failed to monomorphize with instance {inst:?} due to {e:?}"),
            )
        })
}

pub enum TyAsFnResult<'tcx> {
    Resolved {
        def_id: DefId,
        generic_args: GenericArgsRef<'tcx>,
    },
    FnPtr,
    NotAFunction,
}

impl<'tcx> TyAsFnResult<'tcx> {
    pub fn unwrap(self) -> (DefId, GenericArgsRef<'tcx>) {
        match self {
            TyAsFnResult::Resolved {
                def_id,
                generic_args,
            } => (def_id, generic_args),
            TyAsFnResult::FnPtr => panic!("Expected a static function, but got a function pointer"),
            TyAsFnResult::NotAFunction => panic!("Expected a function, but got something else"),
        }
    }

    pub fn to_option(self) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        match self {
            TyAsFnResult::Resolved {
                def_id,
                generic_args,
            } => Some((def_id, generic_args)),
            TyAsFnResult::FnPtr | TyAsFnResult::NotAFunction => None,
        }
    }
}

/// Attempt to interpret this type as a statically determinable function and its
/// generic arguments.
pub fn type_as_fn<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> TyAsFnResult<'tcx> {
    let ty = ty_resolve(ty, tcx);
    match ty.kind() {
        TyKind::FnDef(def_id, generic_args)
        | TyKind::Coroutine(def_id, generic_args)
        | TyKind::Closure(def_id, generic_args) => TyAsFnResult::Resolved {
            def_id: *def_id,
            generic_args,
        },
        TyKind::FnPtr(..) => TyAsFnResult::FnPtr,
        ty => {
            trace!("Bailing from handle_call because func is literal with type: {ty:?}");
            TyAsFnResult::NotAFunction
        }
    }
}

pub fn retype_place<'tcx>(
    orig: Place<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    def_id: DefId,
) -> Place<'tcx> {
    trace!(
        "Retyping {orig:?} in context of {}",
        tcx.def_path_str(def_id)
    );

    let mut new_projection = Vec::new();
    let mut ty = PlaceTy::from_ty(body.local_decls()[orig.local].ty);
    for elem in orig.projection.iter() {
        if matches!(
            ty.ty.kind(),
            TyKind::Alias(..) | TyKind::Param(..) | TyKind::Bound(..) | TyKind::Placeholder(..)
        ) {
            break;
        }

        // Don't continue if we reach a private field. The previous
        // out-of-range silent-skip has been replaced with a hard panic to
        // localize the upstream emitter of the malformed projection — see
        // case-study-sweep-followup-queue.md (queue #3).
        if let ProjectionElem::Field(field, _) = elem
            && let Some(adt_def) = ty.ty.ty_adt_def()
        {
            let Some(field) = adt_def.all_fields().nth(field.as_usize()) else {
                panic!(
                    "[paralegal/retype_place] ADT field index {} out of range for {} \
                     ({} fields, ty {:?})\n\
                     walking projection {:?} of place {:?}\n\
                     in body {} (def_id {:?})\n\
                     backtrace:\n{}",
                    field.as_usize(),
                    tcx.def_path_str(adt_def.did()),
                    adt_def.all_fields().count(),
                    ty.ty,
                    orig.projection,
                    orig,
                    tcx.def_path_str(def_id),
                    def_id,
                    std::backtrace::Backtrace::force_capture(),
                );
            };
            if !field.vis.is_accessible_from(def_id, tcx) {
                break;
            }
        }

        trace!(
            "    Projecting {:?}.{new_projection:?} : {:?} with {elem:?}",
            orig.local, ty.ty,
        );
        ty = ty.projection_ty_core(
            tcx,
            &elem,
            |ty| ty,
            |self_ty, variant_index, field, _| match self_ty.kind() {
                TyKind::Closure(_, args) => {
                    let upvar_tys = args.as_closure().upvar_tys();
                    upvar_tys.iter().nth(field.as_usize()).unwrap_or_else(|| {
                        panic!(
                            "[paralegal/retype_place] closure upvar index {} out of range \
                             ({} upvars, self_ty {:?})\n\
                             walking projection {:?} of place {:?}\n\
                             in body {} (def_id {:?})\n\
                             backtrace:\n{}",
                            field.as_usize(),
                            upvar_tys.len(),
                            self_ty,
                            orig.projection,
                            orig,
                            tcx.def_path_str(def_id),
                            def_id,
                            std::backtrace::Backtrace::force_capture(),
                        )
                    })
                }
                TyKind::Coroutine(_, args) => {
                    let upvar_tys = args.as_coroutine().upvar_tys();
                    upvar_tys.iter().nth(field.as_usize()).unwrap_or_else(|| {
                        panic!(
                            "[paralegal/retype_place] coroutine upvar index {} out of range \
                             ({} upvars, self_ty {:?})\n\
                             walking projection {:?} of place {:?}\n\
                             in body {} (def_id {:?})\n\
                             backtrace:\n{}",
                            field.as_usize(),
                            upvar_tys.len(),
                            self_ty,
                            orig.projection,
                            orig,
                            tcx.def_path_str(def_id),
                            def_id,
                            std::backtrace::Backtrace::force_capture(),
                        )
                    })
                }
                _ => PlaceTy::field_ty(tcx, self_ty, variant_index, field),
            },
            |ty| ty,
        );
        let elem = match elem {
            ProjectionElem::Field(field, _) => ProjectionElem::Field(field, ty.ty),
            elem => elem,
        };
        new_projection.push(elem);
    }

    let p = Place::make(orig.local, &new_projection, tcx);
    trace!("    Final translation: {p:?}");
    p
}

pub fn hashset_join<T: Hash + Eq + PartialEq + Clone>(
    hs1: &mut FxHashSet<T>,
    hs2: &FxHashSet<T>,
) -> bool {
    let orig_len = hs1.len();
    hs1.extend(hs2.iter().cloned());
    hs1.len() != orig_len
}

pub fn hashmap_join<K: Hash + Eq + PartialEq + Clone, V: Clone>(
    hm1: &mut FxHashMap<K, V>,
    hm2: &FxHashMap<K, V>,
    join: impl Fn(&mut V, &V) -> bool,
) -> bool {
    let mut changed = false;
    for (k, v) in hm2 {
        match hm1.entry(k.clone()) {
            Entry::Vacant(slot) => {
                slot.insert(v.clone());
                changed = true;
            }
            Entry::Occupied(mut entry) => {
                changed |= join(entry.get_mut(), v);
            }
        }
    }
    changed
}

pub type BodyAssignments = FxHashMap<Local, Vec<Location>>;

pub fn find_body_assignments(body: &Body<'_>) -> BodyAssignments {
    body.all_locations()
        .filter_map(|location| match body.stmt_at(location) {
            Either::Left(Statement {
                kind: StatementKind::Assign(box (lhs, _)),
                ..
            }) => Some((lhs.as_local()?, location)),
            Either::Right(Terminator {
                kind: TerminatorKind::Call { destination, .. },
                ..
            }) => Some((destination.as_local()?, location)),
            _ => None,
        })
        .into_group_map()
        .into_iter()
        .collect()
}

pub fn ty_resolve<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    match ty.kind() {
        TyKind::Alias(alias_ty) if matches!(alias_ty.kind, AliasTyKind::Opaque { .. }) => {
            tcx.type_of(alias_ty.kind.def_id()).skip_binder()
        }
        _ => ty,
    }
}

pub fn manufacture_substs_for<'tcx>(
    tcx: TyCtxt<'tcx>,
    function: DefId,
) -> Result<GenericArgsRef<'tcx>, ErrorGuaranteed> {
    use rustc_middle::ty::{
        ExistentialPredicate, ExistentialProjection, ExistentialTraitRef, GenericParamDefKind,
        ParamTy, TraitPredicate,
    };

    trace!(?function, "Manufacturing for");

    let tenv = TypingEnv::post_analysis(tcx, function);
    let any_sym = Symbol::intern("Any");

    let generics = tcx.generics_of(function);
    trace!("Found generics {generics:?}");
    let predicates = tcx.predicates_of(function).instantiate_identity(tcx);
    trace!("Found predicates {predicates:?}");
    let lang_items = tcx.lang_items();
    let types = (0..generics.count()).map(|gidx| -> Result<GenericArg<'tcx>, _> {
        let param = generics.param_at(gidx, tcx);
        if let Some(default_val) = param.default_value(tcx) {
            return Ok(tcx.normalize_erasing_regions(tenv, default_val.instantiate_identity()));
        }
        match param.kind {
            // I'm not sure this is correct. We could probably return also "erased" or "static" here.
            GenericParamDefKind::Lifetime => {
                return Ok(GenericArg::from(Region::new_from_kind(
                    tcx,
                    RegionKind::ReErased,
                )));
            }
            GenericParamDefKind::Const { .. } => {
                return Err(tcx.dcx().span_err(
                    tcx.def_span(param.def_id),
                    "Cannot use constants as generic parameters in controllers",
                ));
            }
            GenericParamDefKind::Type { .. } => (),
        };

        let param_as_ty = ParamTy::for_def(param);
        let constraints = predicates.predicates.iter().filter_map(|clause| {
            let clause = tcx.normalize_erasing_regions(tenv, *clause);
            let pred = if let Some(trait_ref) = clause.as_trait_clause() {
                if trait_ref.polarity() != PredicatePolarity::Positive {
                    return None;
                };
                let Some(TraitPredicate { trait_ref, .. }) = trait_ref.no_bound_vars() else {
                    return Some(Err(tcx.dcx().span_err(
                        tcx.def_span(param.def_id),
                        format!("Trait ref had binder {trait_ref:?}"),
                    )));
                };
                if !matches!(trait_ref.self_ty().kind(), TyKind::Param(p) if *p == param_as_ty) {
                    return None;
                };
                if Some(trait_ref.def_id) == lang_items.sized_trait()
                    || tcx.trait_is_auto(trait_ref.def_id)
                {
                    trace!("    bailing because trait is auto trait");
                    return None;
                }
                Some(ExistentialPredicate::Trait(
                    ExistentialTraitRef::erase_self_ty(tcx, trait_ref),
                ))
            } else if let Some(pred) = clause.as_projection_clause() {
                trace!("    is projection clause");
                let Some(pred) = pred.no_bound_vars() else {
                    return Some(Err(tcx.dcx().span_err(
                        tcx.def_span(param.def_id),
                        "Predicate has a bound variable",
                    )));
                };
                if !matches!(pred.self_ty().kind(), TyKind::Param(p) if *p == param_as_ty) {
                    return None;
                };
                Some(ExistentialPredicate::Projection(
                    ExistentialProjection::erase_self_ty(tcx, pred),
                ))
            } else {
                None
            }?;

            Some(Ok(Binder::dummy(pred)))
        });
        let mut predicates = constraints.collect::<Result<Vec<_>, _>>()?;
        trace!("  collected predicates {predicates:?}");
        let no_args: [GenericArg; 0] = [];
        match predicates.len() {
            0 => predicates.push(Binder::dummy(ExistentialPredicate::Trait(
                ExistentialTraitRef::new(
                    tcx,
                    tcx.get_diagnostic_item(any_sym)
                        .expect("The `Any` item is not defined."),
                    no_args,
                ),
            ))),
            1 => (),
            _ => {
                return Err(tcx.dcx().span_err(
                    tcx.def_span(param.def_id),
                    format!(
                        "can only synthesize a trait object for one non-auto trait, got {}",
                        predicates.len()
                    ),
                ));
            }
        };
        let poly_predicate = tcx.mk_poly_existential_predicates_from_iter(predicates.into_iter());
        trace!("  poly predicate {poly_predicate:?}");
        let ty = Ty::new_dynamic(
            tcx,
            poly_predicate,
            Region::new_from_kind(tcx, RegionKind::ReErased),
        );
        Ok(GenericArg::from(ty))
    });
    let new = tcx.mk_args_from_iter(types)?;
    trace!(?new, "finished manufacturing");
    assert_eq!(new.len(), generics.count());
    Ok(new)
}

#[derive(Clone, Copy, Debug, strum::AsRefStr)]
#[strum(serialize_all = "kebab-case")]
pub enum ShimType {
    Once,
    FnPtr,
}

pub enum ShimResult<'tcx> {
    IsHandledShim {
        instance: Instance<'tcx>,
        shim_type: ShimType,
    },
    IsNonHandleableShim,
    IsNotShim,
}

pub fn handle_shims<'tcx>(
    resolved_fn: Instance<'tcx>,
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    span: Span,
) -> ShimResult<'tcx> {
    match resolved_fn.def {
        InstanceKind::ClosureOnceShim { .. } => {
            // Rustc has inserted a call to the shim that maps `Fn` and `FnMut`
            // instances to an `FnOnce`. This shim has no body itself so we
            // can't just inline, we must explicitly simulate it's effects by
            // changing the target function and by setting the calling
            // convention to that of a shim.

            // Because this is a well defined internal item we can make
            // assumptions about its generic arguments.
            let Some((func_a, _rest)) = resolved_fn.args.split_first() else {
                unreachable!()
            };
            let (func_t, g) = match type_as_fn(tcx, func_a.expect_ty()) {
                TyAsFnResult::Resolved {
                    def_id,
                    generic_args,
                } => (def_id, generic_args),
                TyAsFnResult::FnPtr => {
                    return ShimResult::IsNonHandleableShim;
                }
                TyAsFnResult::NotAFunction => {
                    unreachable!("Expected a function, but got something else");
                }
            };
            let instance = Instance::expect_resolve(tcx, typing_env, func_t, g, span);
            ShimResult::IsHandledShim {
                instance,
                shim_type: ShimType::Once,
            }
        }
        InstanceKind::FnPtrShim { .. } => {
            let Some((func_a, _rest)) = resolved_fn.args.split_first() else {
                unreachable!()
            };
            let (func_t, g) = match type_as_fn(tcx, func_a.expect_ty()) {
                TyAsFnResult::Resolved {
                    def_id,
                    generic_args,
                } => (def_id, generic_args),
                TyAsFnResult::FnPtr => {
                    return ShimResult::IsNonHandleableShim;
                }
                TyAsFnResult::NotAFunction => {
                    unreachable!("Expected a function, but got something else");
                }
            };
            let instance = Instance::expect_resolve(tcx, typing_env, func_t, g, span);
            ShimResult::IsHandledShim {
                instance,
                shim_type: ShimType::FnPtr,
            }
        }
        _ => ShimResult::IsNotShim,
    }
}

#[macro_export]
macro_rules! debug_assert_resolved {
    ($e:expr) => {
        #[cfg(debug_assertions)]
        {
            $crate::utils::assert_resolved(&$e, || {
                format!("Expected {:?} to have resolved type", $e)
            });
        }
    };
}

pub fn assert_resolved<'tcx>(rvalue: &impl TypeVisitable<TyCtxt<'tcx>>, msg: impl Fn() -> String) {
    struct V<M>(M);

    impl<'tcx, M: Fn() -> String> TypeVisitor<TyCtxt<'tcx>> for V<M> {
        fn visit_ty(&mut self, ty: Ty<'tcx>) {
            match ty.kind() {
                TyKind::Alias(..) | TyKind::Param(_) => {
                    panic!("Found type variable {ty:?}: {}", (self.0)())
                }
                _ => (),
            }
        }
    }

    let mut v = V(msg);
    rvalue.visit_with(&mut v);
}

// #################################################################################################
// This is a copy of the code in rustc_borrowck::consumers::places_conflict, reproduced here to make
// slight alterations that do not throw an error for nested references
// #################################################################################################

pub struct PlaceConflictContext<'tcx> {
    tcx: TyCtxt<'tcx>,
    unique_ptr_def_id: DefId,
}

#[derive(Clone, Copy)]
pub(crate) enum PlaceOverlap {
    Arbitrary,
    EqualOrDisjoint,
    Disjoint,
}

impl<'tcx> PlaceConflictContext<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let core_sym = rustc_span::Symbol::intern("core");
        let core = tcx
            .crates(())
            .iter()
            .copied()
            .find(|c| tcx.crate_name(*c) == core_sym)
            .expect("core crate not found");
        let find_child = |m, n| {
            let sym = rustc_span::Symbol::intern(n);
            tcx.module_children(m)
                .iter()
                .find(|m| m.ident.name == sym)
                .and_then(|m| m.res.opt_def_id())
                .unwrap_or_else(|| panic!("Could not find module {n}"))
        };
        let ptr_mod = find_child(core.as_def_id(), "ptr");
        let unique_ptr_def_id = find_child(ptr_mod, "Unique");
        Self {
            tcx,
            unique_ptr_def_id,
        }
    }

    fn is_unique_ptr(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            ty::TyKind::Adt(def, _) => def.did() == self.unique_ptr_def_id,
            _ => false,
        }
    }

    /// Helper function for checking if places conflict with a mutable borrow and deep access depth.
    /// This is used to check for places conflicting outside of the borrow checking code (such as in
    /// dataflow).
    pub fn places_conflict(
        &self,
        body: &Body<'tcx>,
        borrow_place: Place<'tcx>,
        access_place: Place<'tcx>,
    ) -> bool {
        let tcx = self.tcx;
        let borrow_local = borrow_place.local;
        let access_local = access_place.local;
        let access_place = access_place.as_ref();

        if borrow_local != access_local {
            // We have proven the borrow disjoint - further projections will remain disjoint.
            return false;
        }

        // This Local/Local case is handled by the more general code below, but
        // it's so common that it's a speed win to check for it first.
        if borrow_place.projection.is_empty() && access_place.projection.is_empty() {
            return true;
        }

        // loop invariant: borrow_c is always either equal to access_c or disjoint from it.
        for ((borrow_place, borrow_c), &access_c) in
            std::iter::zip(borrow_place.iter_projections(), access_place.projection)
        {
            // Borrow and access path both have more components.
            //
            // Examples:
            //
            // - borrow of `a.(...)`, access to `a.(...)`
            // - borrow of `a.(...)`, access to `b.(...)`
            //
            // Here we only see the components we have checked so
            // far (in our examples, just the first component). We
            // check whether the components being borrowed vs
            // accessed are disjoint (as in the second example,
            // but not the first).
            match self.place_projection_conflict(
                body,
                borrow_place,
                borrow_c,
                access_c,
                PlaceConflictBias::Overlap,
            ) {
                PlaceOverlap::Arbitrary => {
                    // We have encountered different fields of potentially
                    // the same union - the borrow now partially overlaps.
                    //
                    // There is no *easy* way of comparing the fields
                    // further on, because they might have different types
                    // (e.g., borrows of `u.a.0` and `u.b.y` where `.0` and
                    // `.y` come from different structs).
                    //
                    // We could try to do some things here - e.g., count
                    // dereferences - but that's probably not a good
                    // idea, at least for now, so just give up and
                    // report a conflict. This is unsafe code anyway so
                    // the user could always use raw pointers.
                    return true;
                }
                PlaceOverlap::EqualOrDisjoint => {
                    // This is the recursive case - proceed to the next element.
                }
                PlaceOverlap::Disjoint => {
                    // We have proven the borrow disjoint - further
                    // projections will remain disjoint.
                    return false;
                }
            }
        }

        if borrow_place.projection.len() > access_place.projection.len() {
            for (base, elem) in borrow_place
                .iter_projections()
                .skip(access_place.projection.len())
            {
                // Borrow path is longer than the access path. Examples:
                //
                // - borrow of `a.b.c`, access to `a.b`
                //
                // Here, we know that the borrow can access a part of
                // our place. This is a conflict if that is a part our
                // access cares about.

                let base_ty = base.ty(body, tcx).ty;

                match (elem, &base_ty.kind()) {
                    (ProjectionElem::Deref, ty::Ref(_, _, hir::Mutability::Not)) => {
                        // This occurs only in two cases. Either we have a reference
                        // as an argument, which causes queries such as
                        // conflicting("(*_1)", "_2") or if we have a raw pointer in
                        // the mix. In the reference case the alias analysis will
                        // already keep track of the conflict. Raw pointers by
                        // themselves are not soundly supported. However this can
                        // also occur via a manual "deref" (or somesuch), on which
                        // case we rely on the lifetimes declared on those functions
                        // to be correct and then our alias analysis will pick it up
                        // correctly.
                        return false;
                    }
                    (ProjectionElem::Deref, _)
                    | (ProjectionElem::Field { .. }, _)
                    | (ProjectionElem::Index { .. }, _)
                    | (ProjectionElem::ConstantIndex { .. }, _)
                    | (ProjectionElem::Subslice { .. }, _)
                    | (ProjectionElem::OpaqueCast { .. }, _)
                    | (ProjectionElem::UnwrapUnsafeBinder(_), _)
                    | (ProjectionElem::Downcast { .. }, _) => {
                        // Recursive case. This can still be disjoint on a
                        // further iteration if this a shallow access and
                        // there's a deref later on, e.g., a borrow
                        // of `*x.y` while accessing `x`.
                    }
                }
            }
        }

        true
    }

    // Given that the bases of `elem1` and `elem2` are always either equal
    // or disjoint (and have the same type!), return the overlap situation
    // between `elem1` and `elem2`.
    fn place_projection_conflict(
        &self,
        body: &Body<'tcx>,
        pi1: PlaceRef<'tcx>,
        pi1_elem: PlaceElem<'tcx>,
        pi2_elem: PlaceElem<'tcx>,
        bias: PlaceConflictBias,
    ) -> PlaceOverlap {
        let tcx = self.tcx;
        match (pi1_elem, pi2_elem) {
            (ProjectionElem::Deref, ProjectionElem::Deref) => {
                // derefs (e.g., `*x` vs. `*x`) - recur.
                PlaceOverlap::EqualOrDisjoint
            }
            (ProjectionElem::OpaqueCast(_), ProjectionElem::OpaqueCast(_)) => {
                // casts to other types may always conflict irrespective of the type being cast to.
                PlaceOverlap::EqualOrDisjoint
            }
            (ProjectionElem::Field(f1, _), ProjectionElem::Field(f2, _)) => {
                if f1 == f2 {
                    // same field (e.g., `a.y` vs. `a.y`) - recur.
                    PlaceOverlap::EqualOrDisjoint
                } else {
                    let ty = pi1.ty(body, tcx).ty;
                    if ty.is_union() {
                        // Different fields of a union, we are basically stuck.
                        PlaceOverlap::Arbitrary
                    } else {
                        // Different fields of a struct (`a.x` vs. `a.y`). Disjoint!
                        PlaceOverlap::Disjoint
                    }
                }
            }
            (ProjectionElem::Downcast(_, v1), ProjectionElem::Downcast(_, v2)) => {
                // different variants are treated as having disjoint fields,
                // even if they occupy the same "space", because it's
                // impossible for 2 variants of the same enum to exist
                // (and therefore, to be borrowed) at the same time.
                //
                // Note that this is different from unions - we *do* allow
                // this code to compile:
                //
                // ```
                // fn foo(x: &mut Result<i32, i32>) {
                //     let mut v = None;
                //     if let Ok(ref mut a) = *x {
                //         v = Some(a);
                //     }
                //     // here, you would *think* that the
                //     // *entirety* of `x` would be borrowed,
                //     // but in fact only the `Ok` variant is,
                //     // so the `Err` variant is *entirely free*:
                //     if let Err(ref mut a) = *x {
                //         v = Some(a);
                //     }
                //     drop(v);
                // }
                // ```
                if v1 == v2 {
                    PlaceOverlap::EqualOrDisjoint
                } else {
                    PlaceOverlap::Disjoint
                }
            }
            (
                ProjectionElem::Index(..),
                ProjectionElem::Index(..)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. },
            )
            | (
                ProjectionElem::ConstantIndex { .. } | ProjectionElem::Subslice { .. },
                ProjectionElem::Index(..),
            ) => {
                // Array indexes (`a[0]` vs. `a[i]`). These can either be disjoint
                // (if the indexes differ) or equal (if they are the same).
                match bias {
                    PlaceConflictBias::Overlap => {
                        // If we are biased towards overlapping, then this is the recursive
                        // case that gives "equal *or* disjoint" its meaning.
                        PlaceOverlap::EqualOrDisjoint
                    }
                    PlaceConflictBias::NoOverlap => {
                        // If we are biased towards no overlapping, then this is disjoint.
                        PlaceOverlap::Disjoint
                    }
                }
            }
            (
                ProjectionElem::ConstantIndex {
                    offset: o1,
                    min_length: _,
                    from_end: false,
                },
                ProjectionElem::ConstantIndex {
                    offset: o2,
                    min_length: _,
                    from_end: false,
                },
            )
            | (
                ProjectionElem::ConstantIndex {
                    offset: o1,
                    min_length: _,
                    from_end: true,
                },
                ProjectionElem::ConstantIndex {
                    offset: o2,
                    min_length: _,
                    from_end: true,
                },
            ) => {
                if o1 == o2 {
                    PlaceOverlap::EqualOrDisjoint
                } else {
                    PlaceOverlap::Disjoint
                }
            }
            (
                ProjectionElem::ConstantIndex {
                    offset: offset_from_begin,
                    min_length: min_length1,
                    from_end: false,
                },
                ProjectionElem::ConstantIndex {
                    offset: offset_from_end,
                    min_length: min_length2,
                    from_end: true,
                },
            )
            | (
                ProjectionElem::ConstantIndex {
                    offset: offset_from_end,
                    min_length: min_length1,
                    from_end: true,
                },
                ProjectionElem::ConstantIndex {
                    offset: offset_from_begin,
                    min_length: min_length2,
                    from_end: false,
                },
            ) => {
                // both patterns matched so it must be at least the greater of the two
                let min_length = std::cmp::max(min_length1, min_length2);
                // `offset_from_end` can be in range `[1..min_length]`, 1 indicates the last
                // element (like -1 in Python) and `min_length` the first.
                // Therefore, `min_length - offset_from_end` gives the minimal possible
                // offset from the beginning
                if offset_from_begin >= min_length - offset_from_end {
                    PlaceOverlap::EqualOrDisjoint
                } else {
                    PlaceOverlap::Disjoint
                }
            }
            (
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length: _,
                    from_end: false,
                },
                ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: false,
                },
            )
            | (
                ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: false,
                },
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length: _,
                    from_end: false,
                },
            ) => {
                if (from..to).contains(&offset) {
                    PlaceOverlap::EqualOrDisjoint
                } else {
                    PlaceOverlap::Disjoint
                }
            }
            (
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length: _,
                    from_end: false,
                },
                ProjectionElem::Subslice { from, .. },
            )
            | (
                ProjectionElem::Subslice { from, .. },
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length: _,
                    from_end: false,
                },
            ) => {
                if offset >= from {
                    PlaceOverlap::EqualOrDisjoint
                } else {
                    PlaceOverlap::Disjoint
                }
            }
            (
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length: _,
                    from_end: true,
                },
                ProjectionElem::Subslice {
                    to, from_end: true, ..
                },
            )
            | (
                ProjectionElem::Subslice {
                    to, from_end: true, ..
                },
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length: _,
                    from_end: true,
                },
            ) => {
                if offset > to {
                    PlaceOverlap::EqualOrDisjoint
                } else {
                    PlaceOverlap::Disjoint
                }
            }
            (
                ProjectionElem::Subslice {
                    from: f1,
                    to: t1,
                    from_end: false,
                },
                ProjectionElem::Subslice {
                    from: f2,
                    to: t2,
                    from_end: false,
                },
            ) => {
                if f2 >= t1 || f1 >= t2 {
                    PlaceOverlap::Disjoint
                } else {
                    PlaceOverlap::EqualOrDisjoint
                }
            }
            (ProjectionElem::Subslice { .. }, ProjectionElem::Subslice { .. }) => {
                PlaceOverlap::EqualOrDisjoint
            }
            _ if self.matches_box_or_unique_deref(body, pi1, pi1_elem, pi2_elem) => {
                // See `matches_box_or_unique_deref` for what this case is about
                PlaceOverlap::EqualOrDisjoint
            }
            (
                ProjectionElem::Deref
                | ProjectionElem::Field(..)
                | ProjectionElem::Index(..)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::OpaqueCast { .. }
                | ProjectionElem::Subslice { .. }
                | ProjectionElem::UnwrapUnsafeBinder(_)
                | ProjectionElem::Downcast(..),
                _,
            ) => panic!(
                "mismatched projections in place_element_conflict: {:?} and {:?}",
                pi1_elem, pi2_elem
            ),
        }
    }

    /// Special case for deref of `Box` and `Unique`
    ///
    /// Basically rustc is sloppy when it comes to boxes. It is perfectly permissible to have the following assignments:
    ///
    /// ```ignore
    /// fn Box::new<T>(_1: T) {
    ///   ...
    ///   _5 = ShallowInitBox(move _4, std::sys::pal::unix::sync::mutex::Mutex);
    ///   (*_5) = move _1;
    ///   _0 = move _5;
    /// }
    /// ```
    ///
    /// This is technically invalid, because `Box` is not a reference (or
    /// pointer) type, but defined as `struct Box<T,
    /// A:Allocator>(Unique<T>, A)`. So technically it should be
    /// `*(_5.0.0)` to get to the contained value.
    ///
    /// Further more we must allow both the `.0` and `.1` field, since it
    /// also tries to match the allocator for conflicts.
    ///
    /// XXX(Justus): This does not try and adjust the the projection
    /// completely as explained above, instead it just matches the deref
    /// to the first projection on right of the assignment. This does not
    /// appear to be a problem at this point, but could cause more
    /// incorrect projections downstream.
    fn matches_box_or_unique_deref(
        &self,
        body: &Body<'tcx>,
        pi1: PlaceRef<'tcx>,
        pi1_elem: PlaceElem<'tcx>,
        pi2_elem: PlaceElem<'tcx>,
    ) -> bool {
        match (pi1_elem, pi2_elem) {
            (ProjectionElem::Deref, ProjectionElem::Field(idx, _))
            | (ProjectionElem::Field(idx, _), ProjectionElem::Deref)
                if matches!(idx.as_u32(), 0 | 1) =>
            {
                let t = pi1.ty(body, self.tcx).ty;
                t.is_box() || self.is_unique_ptr(t)
            }
            _ => false,
        }
    }
}
