//! Utility functions, general purpose structs and extension traits

extern crate smallvec;
use thiserror::Error;

use smallvec::SmallVec;

use crate::{
    desc::Identifier,
    rust::{
        ast,
        hir::{
            self,
            def::Res,
            def_id::{DefId, LocalDefId},
            hir_id::HirId,
            BodyId,
        },
        mir::{self, Location, Place, ProjectionElem, Statement, Terminator},
        rustc_borrowck::consumers::BodyWithBorrowckFacts,
        rustc_data_structures::intern::Interned,
        rustc_span::{symbol::Ident, Span},
        rustc_target::spec::abi::Abi,
        ty,
    },
    rustc_span::ErrorGuaranteed,
    Either, HashMap, HashSet, Symbol, TyCtxt,
};

pub use flowistry::pdg::FnResolution;

use std::cmp::Ordering;
use std::{cell::RefCell, default::Default, hash::Hash, pin::Pin};

pub mod resolve;

mod print;

pub use print::*;

pub use paralegal_spdg::{ShortHash, TinyBitSet};

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

pub trait FnResolutionExt<'tcx> {
    /// Get the most precise type signature we can for this function, erase any
    /// regions and discharge binders.
    ///
    /// Returns an error if it was impossible to get any signature.
    ///
    /// Emits warnings if a precise signature could not be obtained or there
    /// were type variables not instantiated.
    fn sig(self, tcx: TyCtxt<'tcx>) -> Result<ty::FnSig<'tcx>, ErrorGuaranteed>;
}

impl<'tcx> FnResolutionExt<'tcx> for FnResolution<'tcx> {
    fn sig(self, tcx: TyCtxt<'tcx>) -> Result<ty::FnSig<'tcx>, ErrorGuaranteed> {
        let sess = tcx.sess;
        let def_id = self.def_id();
        let def_span = tcx.def_span(def_id);
        let fn_kind = FunctionKind::for_def_id(tcx, def_id)?;
        let late_bound_sig = match (self, fn_kind) {
            (FnResolution::Final(sub), FunctionKind::Generator) => {
                let gen = sub.args.as_generator();
                ty::Binder::dummy(ty::FnSig {
                    inputs_and_output: tcx.mk_type_list(&[gen.resume_ty(), gen.return_ty()]),
                    c_variadic: false,
                    unsafety: hir::Unsafety::Normal,
                    abi: Abi::Rust,
                })
            }
            (FnResolution::Final(sub), FunctionKind::Closure) => sub.args.as_closure().sig(),
            (FnResolution::Final(sub), FunctionKind::Plain) => {
                sub.ty(tcx, ty::ParamEnv::reveal_all()).fn_sig(tcx)
            }
            (FnResolution::Partial(_), FunctionKind::Closure) => {
                if let Some(local) = def_id.as_local() {
                    sess.span_warn(
                        def_span,
                        "Precise variable instantiation for \
                            closure not known, using user type annotation.",
                    );
                    let sig = tcx.closure_user_provided_sig(local);
                    Ok(sig.value)
                } else {
                    Err(sess.span_err(
                        def_span,
                        format!(
                            "Could not determine type signature for external closure {def_id:?}"
                        ),
                    ))
                }?
            }
            (FnResolution::Partial(_), FunctionKind::Generator) => Err(sess.span_err(
                def_span,
                format!(
                    "Cannot determine signature of generator {def_id:?} without monomorphization"
                ),
            ))?,
            (FnResolution::Partial(_), FunctionKind::Plain) => {
                let sig = tcx.fn_sig(def_id);
                sig.no_bound_vars().unwrap_or_else(|| {
                        sess.span_warn(def_span, format!("Cannot discharge bound variables for {sig:?}, they will not be considered by the analysis"));
                        sig.skip_binder()
                    })
            }
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
enum FunctionKind {
    Closure,
    Generator,
    Plain,
}

impl FunctionKind {
    fn for_def_id(tcx: TyCtxt, def_id: DefId) -> Result<Self, ErrorGuaranteed> {
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
    ) -> Result<
        (
            FnResolution<'tcx>,
            SimplifiedArguments<'tcx>,
            mir::Place<'tcx>,
        ),
        AsFnAndArgsErr<'tcx>,
    >;
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
    #[error("function instance could not be resolved")]
    InstanceResolutionErr,
}

impl<'tcx> AsFnAndArgs<'tcx> for mir::Terminator<'tcx> {
    fn as_instance_and_args(
        &self,
        tcx: TyCtxt<'tcx>,
    ) -> Result<
        (
            FnResolution<'tcx>,
            SimplifiedArguments<'tcx>,
            mir::Place<'tcx>,
        ),
        AsFnAndArgsErr<'tcx>,
    > {
        let mir::TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &self.kind
        else {
            return Err(AsFnAndArgsErr::NotAFunctionCall);
        };
        let ty = match &func.constant().ok_or(AsFnAndArgsErr::NotAConstant)?.literal {
            mir::ConstantKind::Val(_, ty) => *ty,
            mir::ConstantKind::Ty(cst) => cst.ty(),
            mir::ConstantKind::Unevaluated { .. } => unreachable!(),
        };
        let (ty::FnDef(defid, gargs) | ty::Closure(defid, gargs)) = ty.kind() else {
            return Err(AsFnAndArgsErr::NotFunctionType(ty.kind().clone()));
        };
        let instance = match test_generics_normalization(tcx, gargs) {
            Err(e) => {
                tcx.sess.span_warn(
                    self.source_info.span,
                    format!(
                        "Could not resolve instance for this call due to {e:?}, \
                        using partial resolution."
                    ),
                );
                FnResolution::Partial(*defid)
            }
            Ok(_) => ty::Instance::resolve(tcx, ty::ParamEnv::reveal_all(), *defid, gargs)
                .map_err(|_| AsFnAndArgsErr::InstanceResolutionErr)?
                .map_or(FnResolution::Partial(*defid), FnResolution::Final),
        };
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

/// Return the places that are read in this statements and possible ref/deref
/// un-layerings of those places.
///
/// XXX(Justus) This part of the algorithms/API I am a bit hazy about. I haven't
/// quite worked out what this soundly means myself.
pub fn read_places_with_provenance<'tcx>(
    l: Location,
    stmt: &Either<&Statement<'tcx>, &Terminator<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> impl Iterator<Item = Place<'tcx>> {
    places_read(tcx, l, stmt, None).flat_map(move |place| place.provenance(tcx).into_iter())
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
    /// Constructs a set of places that are ref/deref/field un-layerings of the
    /// input place.
    ///
    /// The ordering is starting with the place itself, then successively removing
    /// layers until only the local is left. E.g. `provenance_of(_1.foo.bar) ==
    /// [_1.foo.bar, _1.foo, _1]`
    fn provenance(self, tcx: TyCtxt<'tcx>) -> SmallVec<[Place<'tcx>; 2]>;

    fn simple_overlaps(self, other: Place<'tcx>) -> Overlap<'tcx>;
}

impl<'tcx> PlaceExt<'tcx> for Place<'tcx> {
    fn provenance(self, tcx: TyCtxt<'tcx>) -> SmallVec<[Place<'tcx>; 2]> {
        use rustc_utils::PlaceExt;
        let mut refs: SmallVec<_> = self
            .refs_in_projection()
            .map(|(ptr, _)| Place::from_ref(ptr, tcx))
            .chain([self])
            .collect();
        refs.reverse();
        refs
    }

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

/// Old version of [`places_read`], should be considered deprecated.
pub fn extract_places<'tcx>(
    l: mir::Location,
    body: &mir::Body<'tcx>,
    exclude_return_places_from_call: bool,
) -> HashSet<mir::Place<'tcx>> {
    use mir::visit::Visitor;
    let mut places = HashSet::new();
    let mut vis = PlaceVisitor(|p: &mir::Place<'tcx>| {
        places.insert(*p);
    });
    match body.stmt_at_better_err(l) {
        Either::Right(mir::Terminator {
            kind: mir::TerminatorKind::Call { func, args, .. },
            ..
        }) if exclude_return_places_from_call => std::iter::once(func)
            .chain(args.iter())
            .for_each(|o| vis.visit_operand(o, l)),
        _ => body.basic_blocks[l.block]
            .visitable(l.statement_index)
            .apply(l, &mut vis),
    };
    places
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

/// Get the name of the function for this body as an `Ident`. This handles such
/// cases correctly where the function in question has no proper name, as is the
/// case for closures.
///
/// You should probably use [`unique_and_terse_body_name_pls`] instead, as it
/// avoids name clashes.
pub fn body_name_pls<I: IntoLocalDefId>(tcx: TyCtxt, id: I) -> Ident {
    let map = tcx.hir();
    let def_id = id.into_local_def_id(tcx);
    let node = map.find_by_def_id(def_id).unwrap();
    node.ident()
        .or_else(|| {
            matches!(
                node,
                hir::Node::Expr(hir::Expr {
                    kind: hir::ExprKind::Closure(..),
                    ..
                })
            )
            .then(|| {
                let owner = map.enclosing_body_owner(map.local_def_id_to_hir_id(def_id));
                Ident::from_str(&(body_name_pls(tcx, owner).to_string() + "_closure"))
            })
        })
        .unwrap_or_else(|| panic!("Node {node:?} could not be named"))
}

/// Gives a string name for this i that is free of name clashes, as it
/// includes a hash of the id.
pub fn unique_and_terse_body_name_pls<I: IntoLocalDefId>(tcx: TyCtxt, id: I) -> Symbol {
    let def_id = id.into_local_def_id(tcx);
    let ident = body_name_pls(tcx, def_id);
    Symbol::intern(&format!("{}_{}", ident.name, ShortHash::new(def_id)))
}

/// Create a file for dumping an `ext` kind of output for `id`. The name of the
/// resulting file avoids clashes but is also descriptive (uses the resolved
/// name of `id`).
pub fn dump_file_pls<I: IntoLocalDefId>(
    tcx: TyCtxt,
    id: I,
    ext: &str,
) -> std::io::Result<std::fs::File> {
    outfile_pls(format!("{}.{ext}", unique_and_terse_body_name_pls(tcx, id)))
}

/// Give me this file as writable (possibly creating or overwriting it).
///
/// This is just a common pattern of how we want to open files we're writing
/// output to. Literally just implemented as
///
/// ```
/// std::fs::OpenOptions::new()
///     .create(true)
///     .truncate(true)
///     .write(true)
///     .open(path)
/// ```
pub fn outfile_pls<P: AsRef<std::path::Path>>(path: P) -> std::io::Result<std::fs::File> {
    std::fs::OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .open(path)
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

/// Return all places mentioned at this location that are *read*. Which means
/// that if a `Place` is not read but assigned (e.g. the return place of a
/// function call), it will not be in the result set.
pub fn places_read<'tcx>(
    tcx: TyCtxt<'tcx>,
    location: mir::Location,
    stmt: &Either<&mir::Statement<'tcx>, &mir::Terminator<'tcx>>,
    read_after: Option<mir::Place<'tcx>>,
) -> impl Iterator<Item = mir::Place<'tcx>> {
    use mir::visit::Visitor;
    let mut places = HashSet::new();
    let mut vis = PlaceVisitor(|p: &mir::Place<'tcx>| {
        places.insert(*p);
    });
    match stmt {
        // TODO: This needs to deal with fields!!
        Either::Left(mir::Statement {
            kind: mir::StatementKind::Assign(a),
            ..
        }) => {
            let mut proj = a.0.iter_projections();
            // We advance the iterator from the end until we find a projection
            // that might not return the full object, e.g. field access or
            // indexing.
            //
            // `iter_projections` returns an iterator of successively more
            // projections, e.g. it starts with the local itself, like `_1` and
            // then adds on e.g. `*_1`, `(*_1).foo` etc.
            //
            // We advance from the end because we want to basically drop
            // everything that is more specific. As an example if you had
            // `*((*_1).foo) = bla` then only the `foo` field gets modified, so
            // `_1` *and* `*_1` should still be considered read, but we can't
            // just do "filter" or the last `*` will cause `((*_1).foo, *)` to
            // end up in the result as well (leakage).
            let last_field_proj = proj.rfind(|pl| pl.1.may_be_indirect());
            // Now we iterate over the rest, including the field projection we
            // found, because we only consider the first part of the tuple (a
            // `PlaceRef`) which contains a place *up to* the projection in the
            // second part of the tuple (which is what our condition was on)>
            for pl in proj.chain(last_field_proj.into_iter()) {
                vis.visit_place(
                    &<Place as rustc_utils::PlaceExt>::from_ref(pl.0, tcx),
                    mir::visit::PlaceContext::MutatingUse(mir::visit::MutatingUseContext::Store),
                    location,
                );
            }
            if let mir::Rvalue::Aggregate(_, ops) = &a.1 {
                match handle_aggregate_assign(a.0, &a.1, tcx, &ops.raw, read_after) {
                    Ok(place) => vis.visit_place(
                        &place,
                        mir::visit::PlaceContext::NonMutatingUse(
                            mir::visit::NonMutatingUseContext::Move,
                        ),
                        location,
                    ),
                    Err(e) => {
                        debug!("handle_aggregate_assign threw {e}");
                        vis.visit_rvalue(&a.1, location);
                    }
                }
            } else {
                vis.visit_rvalue(&a.1, location);
            }
        }
        Either::Right(term) => vis.visit_terminator(term, location), // TODO this is not correct
        _ => (),
    };
    places.into_iter()
}

fn handle_aggregate_assign<'tcx>(
    place: mir::Place<'tcx>,
    _rvalue: &mir::Rvalue<'tcx>,
    tcx: TyCtxt<'tcx>,
    ops: &[mir::Operand<'tcx>],
    read_after: Option<mir::Place<'tcx>>,
) -> Result<mir::Place<'tcx>, &'static str> {
    let read_after = read_after.ok_or("no read after provided")?;
    let inner_project = &read_after.projection[place.projection.len()..];
    let (field, rest_project) = inner_project.split_first().ok_or("projection too short")?;
    let f = if let mir::ProjectionElem::Field(f, _) = field {
        f
    } else {
        return Err("Not a field projection");
    };
    Ok(ops[f.as_usize()]
        .place()
        .ok_or("Constant")?
        .project_deeper(rest_project, tcx))
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

/// Creates an `Identifier` for this `HirId`
pub fn unique_identifier_for_item<D: IntoDefId + Hash + Copy>(tcx: TyCtxt, did: D) -> Identifier {
    let did = did.into_def_id(tcx);
    let get_parent = || unique_identifier_for_item(tcx, tcx.parent(did));
    Identifier::new_intern(&format!(
        "{}_{}",
        tcx.opt_item_name(did)
            .map(|n| n.to_string())
            .or_else(|| {
                use hir::def::DefKind::*;
                match tcx.def_kind(did) {
                    OpaqueTy => Some("opaque".to_string()),
                    Closure => Some(format!("{}_closure", get_parent())),
                    Generator => Some(format!("{}_generator", get_parent())),
                    _ => None,
                }
            })
            .unwrap_or_else(|| panic!(
                "Could not name {} {:?}",
                tcx.def_path_debug_str(did),
                tcx.def_kind(did)
            )),
        ShortHash::new(did),
    ))
}

#[derive(Error, Debug)]
pub enum BodyResolutionError {
    #[error("not a function-like object")]
    /// The provided id did not refer to a function-like object.
    NotAFunction,
    #[error("body not available")]
    /// The provided id refers to an external entity and we have no access to
    /// its body
    External,
    /// The function refers to a trait item (not an `impl` item or raw `fn`)
    #[error("is associated function of trait {0:?}")]
    IsTraitAssocFn(DefId),
}

/// Extension trait for [`TyCtxt`]
pub trait TyCtxtExt<'tcx> {
    /// Resolve this [`DefId`] to a body. Returns
    /// [`BodyWithBorrowckFacts`](crate::rust::rustc_borrowck::BodyWithBorrowckFacts),
    /// because it internally uses flowistry's body resolution
    /// ([`rustc_utils::mir::borrowck_facts::get_body_with_borrowck_facts`]) which
    /// memoizes its results so this is actually a cheap query.
    ///
    /// Returns `None` if the id does not refer to a function or if its body is
    /// unavailable.
    fn body_for_def_id(
        self,
        local_def_id: LocalDefId,
    ) -> Result<&'tcx BodyWithBorrowckFacts<'tcx>, BodyResolutionError>;

    /// Essentially the same as [`Self::body_for_def_id`] but handles errors
    /// according to our default policy which is as follows:
    ///
    /// - [`BodyResolutionError::NotAFunction`]: Hard error (panic). We consider
    ///       this an ICE because calling this method on a non-function `DefId`
    ///       could indicate errors elsewhere in the compiler.
    /// - [`BodyResolutionError::External`]: Silent because otherwise we would
    ///       spam warnings.
    /// - [`BodyResolutionError::IsTraitAssocFn`]: Warning emitted, because this
    ///       is probably caused by `dyn`, which we can't resolve even if it's
    ///       crate-local and that might be surprising.
    fn body_for_def_id_default_policy(
        self,
        local_def_id: LocalDefId,
    ) -> Option<&'tcx BodyWithBorrowckFacts<'tcx>>;
}

impl<'tcx> TyCtxtExt<'tcx> for TyCtxt<'tcx> {
    fn body_for_def_id(
        self,
        local_def_id: LocalDefId,
    ) -> Result<&'tcx BodyWithBorrowckFacts<'tcx>, BodyResolutionError> {
        let def_kind = self.def_kind(local_def_id);
        if !def_kind.is_fn_like() {
            return Err(BodyResolutionError::NotAFunction);
        }
        if let Some(trt) = is_non_default_trait_method(self, local_def_id.to_def_id()) {
            return Err(BodyResolutionError::IsTraitAssocFn(trt));
        }
        Ok(rustc_utils::mir::borrowck_facts::get_body_with_borrowck_facts(self, local_def_id))
    }

    fn body_for_def_id_default_policy(
        self,
        local_def_id: LocalDefId,
    ) -> Option<&'tcx BodyWithBorrowckFacts<'tcx>> {
        match self.body_for_def_id(local_def_id) {
            Ok(b) => Some(b),
            Err(e) => {
                let sess = self.sess;
                match e {
                    BodyResolutionError::External => (),
                    BodyResolutionError::IsTraitAssocFn(r#trait) => {
                        sess.struct_span_warn(
                            self.def_span(local_def_id.to_def_id()),
                            "cannot analyze this function as it is a trait method with \
                            no body (probably caused by the use of `dyn`)",
                        )
                        .span_note(self.def_span(r#trait), "associated trait")
                        .emit();
                    }
                    BodyResolutionError::NotAFunction => {
                        sess.span_fatal(
                            self.def_span(local_def_id.to_def_id()),
                            "this item is not a function",
                        );
                    }
                };
                None
            }
        }
    }
}

pub fn is_non_default_trait_method(tcx: TyCtxt, function: DefId) -> Option<DefId> {
    let assoc_item = tcx.opt_associated_item(function)?;
    if assoc_item.container != ty::AssocItemContainer::TraitContainer
        || assoc_item.defaultness(tcx).has_value()
    {
        return None;
    }
    assoc_item.trait_item_def_id
}

/// A struct that can be used to apply a [`FnMut`] to every [`Place`] in a MIR
/// object via the [`MutVisitor`](mir::visit::MutVisitor) trait. Crucial
/// difference to [`PlaceVisitor`] is that this function can alter the place
/// itself.
pub struct RePlacer<'tcx, F>(TyCtxt<'tcx>, F);

impl<'tcx, F: FnMut(&mut mir::Place<'tcx>)> mir::visit::MutVisitor<'tcx> for RePlacer<'tcx, F> {
    fn tcx<'a>(&'a self) -> TyCtxt<'tcx> {
        self.0
    }
    fn visit_place(
        &mut self,
        place: &mut mir::Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) {
        self.1(place)
    }
}

/// Conveniently create a vector of [`Symbol`]s. This way you can just write
/// `sym_vec!["s1", "s2", ...]` and this macro will make sure to call
/// [`Symbol::intern`]
#[macro_export]
macro_rules! sym_vec {
    ($($e:expr),*) => {
        vec![$(Symbol::intern($e)),*]
    };
}

pub fn with_temporary_logging_level<R, F: FnOnce() -> R>(filter: log::LevelFilter, f: F) -> R {
    let reset_level = log::max_level();
    log::set_max_level(filter);
    let r = f();
    log::set_max_level(reset_level);
    r
}

/// This code is adapted from [`flowistry::cached::Cache`] but with a recursion
/// breaking mechanism. This alters the [`Self::get`] method signature to return
/// an [`Option`] of a reference. In particular the method will return [`None`]
/// if it is called *with the same key* while computing a construction function
/// for that key.
pub struct RecursionBreakingCache<In, Out>(RefCell<HashMap<In, Option<Pin<Box<Out>>>>>);

impl<In, Out> RecursionBreakingCache<In, Out>
where
    In: Hash + Eq + Clone,
    Out: Unpin,
{
    pub fn size(&self) -> usize {
        self.0.borrow().len()
    }
    /// Get or compute the value for this key. Returns `None` if called recursively.
    pub fn get<'a>(&'a self, key: In, compute: impl FnOnce(In) -> Out) -> Option<&'a Out> {
        if !self.0.borrow().contains_key(&key) {
            self.0.borrow_mut().insert(key.clone(), None);
            let out = Pin::new(Box::new(compute(key.clone())));
            self.0.borrow_mut().insert(key.clone(), Some(out));
        }

        let cache = self.0.borrow();
        // Important here to first `unwrap` the `Option` created by `get`, then
        // propagate the potential option stored in the map.
        let entry = cache.get(&key).unwrap().as_ref()?;

        // SAFETY: because the entry is pinned, it cannot move and this pointer will
        // only be invalidated if Cache is dropped. The returned reference has a lifetime
        // equal to Cache, so Cache cannot be dropped before this reference goes out of scope.
        Some(unsafe { std::mem::transmute::<&'_ Out, &'a Out>(&**entry) })
    }
}

impl<In, Out> Default for RecursionBreakingCache<In, Out> {
    fn default() -> Self {
        Self(RefCell::new(HashMap::default()))
    }
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

impl<'tcx> Spanned<'tcx> for DefId {
    fn span(&self, tcx: TyCtxt<'tcx>) -> Span {
        tcx.def_span(*self)
    }
}

impl<'tcx> Spanned<'tcx> for (LocalDefId, mir::Location) {
    fn span(&self, tcx: TyCtxt<'tcx>) -> Span {
        let body = tcx.body_for_def_id(self.0).unwrap();
        (&body.body, self.1).span(tcx)
    }
}
