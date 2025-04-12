//! Utility functions, general purpose structs and extension traits

extern crate smallvec;
use flowistry_pdg::RichLocation;
use flowistry_pdg_construction::utils::type_as_fn;
use thiserror::Error;

use crate::{desc::Identifier, rustc_span::ErrorGuaranteed, Either, Symbol, TyCtxt};
pub use flowistry_pdg_construction::utils::is_virtual;
pub use paralegal_spdg::{ShortHash, TinyBitSet};

use rustc_ast as ast;
use rustc_data_structures::intern::Interned;
use rustc_hir::{
    self as hir,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    hir_id::HirId,
    BodyId,
};
use rustc_middle::{
    mir::{self, Constant, Location, Place, ProjectionElem, Terminator},
    ty::{self, GenericArgsRef, Instance, Ty},
};
use rustc_span::{symbol::Ident, Span as RustSpan, Span};
use rustc_target::spec::abi::Abi;

use std::{cmp::Ordering, hash::Hash};

mod print;
pub mod resolve;

pub use print::*;

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
            ast::AttrKind::Normal(normal) => match &normal.item {
                ast::AttrItem {
                    path: attr_path,
                    args,
                    ..
                } if attr_path.segments.len() == path.len()
                    && attr_path
                        .segments
                        .iter()
                        .zip(path)
                        .all(|(seg, i)| seg.ident.name == *i) =>
                {
                    Some(args)
                }
                _ => None,
            },
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

impl<'tcx> TyExt for ty::Ty<'tcx> {
    fn defid_ref(&self) -> Option<&DefId> {
        match self.kind() {
            ty::TyKind::Adt(ty::AdtDef(Interned(ty::AdtDefData { did, .. }, _)), _) => Some(did),
            ty::TyKind::Foreign(did)
            | ty::TyKind::FnDef(did, _)
            | ty::TyKind::Closure(did, _)
            | ty::TyKind::Generator(did, _, _) => Some(did),
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
        match self.unpack() {
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
        let sess = tcx.sess;
        let def_id = self.def_id();
        let def_span = tcx.def_span(def_id);
        let fn_kind = FunctionKind::for_def_id(tcx, def_id)?;
        let late_bound_sig = match fn_kind {
            FunctionKind::Generator => {
                let gen = self.args.as_generator();
                ty::Binder::dummy(ty::FnSig {
                    inputs_and_output: tcx.mk_type_list(&[gen.resume_ty(), gen.return_ty()]),
                    c_variadic: false,
                    unsafety: hir::Unsafety::Normal,
                    abi: Abi::Rust,
                })
            }
            FunctionKind::Closure => self.args.as_closure().sig(),
            FunctionKind::Plain => self.ty(tcx, ty::ParamEnv::reveal_all()).fn_sig(tcx),
        };
        Ok(tcx
            .try_normalize_erasing_late_bound_regions(ty::ParamEnv::reveal_all(), late_bound_sig)
            .unwrap_or_else(|e| {
                sess.span_warn(
                    def_span,
                    format!("Could not erase regions in {late_bound_sig:?}: {e:?}"),
                );
                late_bound_sig.skip_binder()
            }))
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
        if tcx.generator_kind(def_id).is_some() {
            Ok(Self::Generator)
        } else if tcx.is_closure(def_id) {
            Ok(Self::Closure)
        } else if tcx.def_kind(def_id).is_fn_like() {
            Ok(Self::Plain)
        } else {
            Err(tcx
                .sess
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

pub fn ty_of_const<'tcx>(c: &Constant<'tcx>) -> Ty<'tcx> {
    match c.literal {
        mir::ConstantKind::Val(_, ty) => ty,
        mir::ConstantKind::Ty(cst) => cst.ty(),
        mir::ConstantKind::Unevaluated { .. } => unreachable!(),
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
            return Err(AsFnAndArgsErr::NotFunctionType(ty.kind().clone()));
        };
        test_generics_normalization(tcx, gargs)
            .map_err(|e| AsFnAndArgsErr::NormalizationError(format!("{e:?}")))?;
        let instance = ty::Instance::resolve(tcx, ty::ParamEnv::reveal_all(), def_id, gargs)
            .map_err(|_| AsFnAndArgsErr::InstanceResolutionErr)?
            .ok_or(AsFnAndArgsErr::InstanceTooUnspecific)?;
        Ok((
            instance,
            args.iter().map(|a| a.place()).collect(),
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
    tcx.try_normalize_erasing_regions(ty::ParamEnv::reveal_all(), args)
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

pub enum Overlap<'tcx> {
    Equal,
    Independent,
    Parent(&'tcx [mir::PlaceElem<'tcx>]),
    Child(&'tcx [mir::PlaceElem<'tcx>]),
}

impl<'tcx> Overlap<'tcx> {
    pub fn contains_other(self) -> bool {
        matches!(self, Overlap::Equal | Overlap::Parent(_))
    }
}

/// Extension trait for [`Place`]s so we can implement methods on them. [`Self`]
/// is only ever supposed to be instantiated as [`Place`].
pub trait PlaceExt<'tcx> {
    fn simple_overlaps(self, other: Place<'tcx>) -> Overlap<'tcx>;
}

impl<'tcx> PlaceExt<'tcx> for Place<'tcx> {
    fn simple_overlaps(self, other: Place<'tcx>) -> Overlap<'tcx> {
        if self.local != other.local
            || self
                .projection
                .iter()
                .zip(other.projection)
                .any(|(one, other)| one != other)
        {
            return Overlap::Independent;
        }
        match self.projection.len().cmp(&other.projection.len()) {
            Ordering::Less => Overlap::Parent(&other.projection[self.projection.len()..]),
            Ordering::Greater => Overlap::Child(&self.projection[other.projection.len()..]),
            Ordering::Equal => Overlap::Equal,
        }
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
                ident,
                owner_id,
                kind: hir::ItemKind::Fn(_, _, body_id),
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
                tcx.hir().body_owner_def_id(*body_id),
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
        tcx.hir().body_owner_def_id(self)
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
        tcx.hir().body_owner_def_id(self).into_def_id(tcx)
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

pub trait IntoHirId: std::marker::Sized {
    fn into_hir_id(self, tcx: TyCtxt) -> Option<HirId>;

    #[inline]
    fn force_into_hir_id(self, tcx: TyCtxt) -> HirId {
        self.into_hir_id(tcx).unwrap()
    }
}

impl IntoHirId for LocalDefId {
    #[inline]
    fn into_hir_id(self, tcx: TyCtxt) -> Option<HirId> {
        Some(tcx.hir().local_def_id_to_hir_id(self))
    }
}

/// Get a reasonable, but not guaranteed unique name for this item
pub fn identifier_for_item<D: IntoDefId + Hash + Copy>(tcx: TyCtxt, did: D) -> Identifier {
    // TODO Make a generic version instead of just copying `unique_identifier_for_item`
    let did = did.into_def_id(tcx);
    let get_parent = || identifier_for_item(tcx, tcx.parent(did));
    Identifier::new_intern(
        &tcx.opt_item_name(did)
            .map(|n| n.to_string())
            .or_else(|| {
                use hir::def::DefKind::*;
                match tcx.def_kind(did) {
                    OpaqueTy => Some("Opaque".to_string()),
                    Closure => Some(format!("{}_closure", get_parent())),
                    Generator => Some(format!("{}_generator", get_parent())),
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

pub fn with_temporary_logging_level<R, F: FnOnce() -> R>(filter: log::LevelFilter, f: F) -> R {
    let reset_level = log::max_level();
    log::set_max_level(filter);
    let r = f();
    log::set_max_level(reset_level);
    r
}

pub fn time<R, F: FnOnce() -> R>(msg: &str, f: F) -> R {
    info!("Starting {msg}");
    let time = std::time::Instant::now();
    let r = f();
    info!("{msg} took {}", humantime::format_duration(time.elapsed()));
    r
}

pub trait IntoBodyId: Copy {
    fn into_body_id(self, tcx: TyCtxt) -> Option<BodyId>;
}

impl IntoBodyId for BodyId {
    fn into_body_id(self, _tcx: TyCtxt) -> Option<BodyId> {
        Some(self)
    }
}

impl IntoBodyId for HirId {
    fn into_body_id(self, tcx: TyCtxt) -> Option<BodyId> {
        self.as_owner()?.def_id.into_body_id(tcx)
    }
}

impl IntoBodyId for LocalDefId {
    fn into_body_id(self, tcx: TyCtxt) -> Option<BodyId> {
        tcx.hir().maybe_body_owned_by(self)
    }
}

impl IntoBodyId for DefId {
    fn into_body_id(self, tcx: TyCtxt) -> Option<BodyId> {
        self.as_local()?.into_body_id(tcx)
    }
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
