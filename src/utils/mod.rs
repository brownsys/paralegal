//! Utility functions, general purpose structs and extension traits

extern crate smallvec;

use hir::def::Res;
use smallvec::SmallVec;

use crate::{
    desc::Identifier,
    rust::{
        ast,
        hir::{
            self,
            def_id::{DefId, LocalDefId},
            hir_id::HirId,
            BodyId,
        },
        mir::{self, Location, Place, ProjectionElem, Statement, Terminator},
        rustc_data_structures::fx::{FxHashMap, FxHashSet},
        rustc_span::symbol::Ident,
        ty,
    },
    Either, HashMap, HashSet, Symbol, TyCtxt,
};

use std::{borrow::Cow, cell::RefCell, default::Default, hash::Hash, pin::Pin};

pub mod resolve;

mod print;
pub use print::*;

pub mod tiny_bitset;
pub use tiny_bitset::TinyBitSet;

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
    fn match_extract<A, F: Fn(&ast::MacArgs) -> A>(&self, path: &[Symbol], parse: F) -> Option<A>;
    /// Check that this attribute matches the provided path. All attribute
    /// payload is ignored (i.e. no error if there is a payload).
    fn matches_path(&self, path: &[Symbol]) -> bool {
        self.match_extract(path, |_| ()).is_some()
    }
}

impl MetaItemMatch for ast::Attribute {
    fn match_extract<A, F: Fn(&ast::MacArgs) -> A>(&self, path: &[Symbol], parse: F) -> Option<A> {
        match &self.kind {
            ast::AttrKind::Normal(
                ast::AttrItem {
                    path: attr_path,
                    args,
                    ..
                },
                _,
            ) if attr_path.segments.len() == path.len()
                && attr_path
                    .segments
                    .iter()
                    .zip(path)
                    .all(|(seg, i)| seg.ident.name == *i) =>
            {
                Some(parse(args))
            }
            _ => None,
        }
    }
}

/// Extension trait for [`ty::Ty`]. This lets us implement methods on
/// [`ty::Ty`]. [`Self`] is only ever supposed to be instantiated as [`ty::Ty`].
pub trait TyExt {
    /// Extract a `DefId` if this type references an object that has one. This
    /// is true for most user defined types, including types form the standard
    /// library, but not builtin types, such as `u32`, arrays or ad-hoc types
    /// such as function pointers.
    ///
    /// Use with caution, this function might not be exhaustive (yet).
    fn defid(self) -> Option<DefId>;
}

impl<'tcx> TyExt for ty::Ty<'tcx> {
    fn defid(self) -> Option<DefId> {
        match self.kind() {
            ty::TyKind::Adt(def, _) => Some(def.did()),
            ty::TyKind::Foreign(did)
            | ty::TyKind::FnDef(did, _)
            | ty::TyKind::Closure(did, _)
            | ty::TyKind::Generator(did, _, _)
            | ty::TyKind::Opaque(did, _) => Some(*did),
            _ => None,
        }
    }
}

pub trait GenericArgExt<'tcx> {
    /// Generic arguments can reference non-type things (in particular constants
    /// and lifetimes). If it is a type, then this extracts that type, otherwise
    /// `None`.
    fn as_type(self) -> Option<ty::Ty<'tcx>>;
}

impl<'tcx> GenericArgExt<'tcx> for ty::subst::GenericArg<'tcx> {
    fn as_type(self) -> Option<ty::Ty<'tcx>> {
        match self.unpack() {
            ty::subst::GenericArgKind::Type(t) => Some(t),
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
            .basic_blocks()
            .get(block)
            .ok_or_else(|| StmtAtErr::BasicBlockOutOfBound(block, &self))?;
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
    ) -> Result<
        (
            DefId,
            SimplifiedArguments<'tcx>,
            Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        ),
        AsFnAndArgsErr<'tcx>,
    >;
}

impl<'tcx> AsFnAndArgs<'tcx> for mir::Terminator<'tcx> {
    fn as_fn_and_args(
        &self,
    ) -> Result<
        (
            DefId,
            SimplifiedArguments<'tcx>,
            Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        ),
        AsFnAndArgsErr<'tcx>,
    > {
        self.kind.as_fn_and_args()
    }
}

#[derive(Debug)]
pub enum AsFnAndArgsErr<'tcx> {
    NotAConstant,
    NotFunctionType(ty::TyKind<'tcx>),
    NotValueLevelConstant(ty::Const<'tcx>),
    NotAFunctionCall,
}

impl<'tcx> AsFnAndArgs<'tcx> for mir::TerminatorKind<'tcx> {
    fn as_fn_and_args(
        &self,
    ) -> Result<
        (
            DefId,
            SimplifiedArguments<'tcx>,
            Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        ),
        AsFnAndArgsErr<'tcx>,
    > {
        match self {
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                let defid = match func.constant().ok_or(AsFnAndArgsErr::NotAConstant)? {
                    mir::Constant { literal, .. } => match literal {
                        mir::ConstantKind::Val(_, ty)
                        | mir::ConstantKind::Ty(ty::Const(
                            crate::rust::rustc_data_structures::intern::Interned(
                                ty::ConstS { ty, .. },
                                _,
                            ),
                        )) => match ty.kind() {
                            ty::FnDef(defid, _) | ty::Closure(defid, _) => Ok(*defid),
                            _ => Err(AsFnAndArgsErr::NotFunctionType(ty.kind().clone())),
                        },
                    },
                }?;
                Ok((
                    defid,
                    args.iter().map(|a| a.place()).collect(),
                    *destination,
                ))
            }
            _ => Err(AsFnAndArgsErr::NotAFunctionCall),
        }
    }
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

/// Extension trait for [`Location`]. This lets us implement methods on
/// [`Location`]. [`Self`] is only ever supposed to be instantiated as
/// [`Location`].
pub trait LocationExt {
    /// This function deals with the fact that flowistry uses special locations
    /// to refer to function arguments. Those locations are not recognized the
    /// rustc functions that operate on MIR and thus need to be filtered before
    /// doing things such as indexing into a `mir::Body`.
    fn is_real(self, body: &mir::Body) -> bool;
}

impl LocationExt for Location {
    fn is_real(self, body: &mir::Body) -> bool {
        body.basic_blocks().get(self.block).map(|bb|
                // Its `<=` because if len == statement_index it refers to the
                // terminator
                // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.Location.html
                self.statement_index <= bb.statements.len())
            == Some(true)
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
    places_read(tcx, l, stmt, None)
        .into_iter()
        .flat_map(move |place| place.provenance(tcx).into_iter())
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
}

impl<'tcx> PlaceExt<'tcx> for Place<'tcx> {
    fn provenance(self, tcx: TyCtxt<'tcx>) -> SmallVec<[Place<'tcx>; 2]> {
        use flowistry::mir::utils::PlaceExt;
        let mut refs = self.place_and_refs_in_projection(tcx);
        // Now make sure the ordering is correct. The refs as we get them from above
        // are `[_1.foo.bar, _1, _1.foo]`, e.g. first the place, then the local and
        // then successively more projections.
        //
        // So first we reverse it, because we want successively fewer projections
        refs.reverse();
        // Now we have the right order, except for `place` (e.g. the most specific
        // place) being at the end, so we rotate to get it to the front.
        refs.rotate_right(0);
        refs
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
                def_id,
                kind: hir::ItemKind::Fn(_, _, body_id),
                ..
            })
            | hir::Node::ImplItem(hir::ImplItem {
                ident,
                def_id,
                kind: hir::ImplItemKind::Fn(_, body_id),
                ..
            }) => Some((*ident, *def_id, *body_id)),
            hir::Node::Expr(hir::Expr {
                kind: hir::ExprKind::Closure(_, _, body_id, _, _),
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

/// Old version of [`places_read`](../fn.places_read.html) and
/// [`places_read_with_provenance`](../fn.places_read_with_provenance.html).
/// Should be considered deprecated.
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
        _ => body.basic_blocks()[l.block]
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
    fn into_local_def_id(self, _tcx: TyCtxt) -> LocalDefId {
        self
    }
}

impl IntoLocalDefId for BodyId {
    fn into_local_def_id(self, tcx: TyCtxt) -> LocalDefId {
        tcx.hir().body_owner_def_id(self)
    }
}

impl IntoLocalDefId for HirId {
    fn into_local_def_id(self, tcx: TyCtxt) -> LocalDefId {
        tcx.hir().local_def_id(self)
    }
}

impl<D: Copy + IntoLocalDefId> IntoLocalDefId for &'_ D {
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
    Symbol::intern(&format!("{}_{:x}", ident.name, short_hash_pls(def_id)))
}

/// Create a file for dumping an `ext` kind of output for `id`. The name of the
/// resulting file avoids clashes but is also descriptive (uses the resolved
/// name of `id`).
pub fn dump_file_pls<I: IntoLocalDefId>(
    tcx: TyCtxt,
    id: I,
    ext: &str,
) -> std::io::Result<std::fs::File> {
    outfile_pls(&format!(
        "{}.{ext}",
        unique_and_terse_body_name_pls(tcx, id)
    ))
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
                    &<Place as flowistry::mir::utils::PlaceExt>::from_ref(pl.0, tcx),
                    mir::visit::PlaceContext::MutatingUse(mir::visit::MutatingUseContext::Store),
                    location,
                );
            }
            if let mir::Rvalue::Aggregate(_, ops) = &a.1 {
                match handle_aggregate_assign(a.0, &a.1, tcx, ops, read_after) {
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

/// Brother to [`IntoLocalDefId`], converts the id type to a [`DefId`] using [`TyCtxt`]
pub trait IntoDefId {
    fn into_def_id(self, tcx: TyCtxt) -> DefId;
}

impl IntoDefId for DefId {
    fn into_def_id(self, tcx: TyCtxt) -> DefId {
        self
    }
}

impl IntoDefId for LocalDefId {
    fn into_def_id(self, tcx: TyCtxt) -> DefId {
        self.to_def_id()
    }
}

impl IntoDefId for HirId {
    fn into_def_id(self, tcx: TyCtxt) -> DefId {
        tcx.hir().local_def_id(self).to_def_id()
    }
}

impl<D: Copy + IntoDefId> IntoDefId for &'_ D {
    fn into_def_id(self, tcx: TyCtxt) -> DefId {
        (*self).into_def_id(tcx)
    }
}

impl IntoDefId for BodyId {
    fn into_def_id(self, tcx: TyCtxt) -> DefId {
        tcx.hir().body_owner_def_id(self).into_def_id(tcx)
    }
}

impl IntoDefId for Res {
    fn into_def_id(self, tcx: TyCtxt) -> DefId {
        match self {
            Res::Def(_, did) => did,
            _ => panic!("turning non-def res into DefId; res is: {:?}", self),
        }
    }
}

/// Creates an `Identifier` for this `HirId`
pub fn identifier_for_item<D: IntoDefId + Hash + Copy>(tcx: TyCtxt, did: D) -> Identifier {
	let did = did.into_def_id(tcx);
    Identifier::from_str(&format!(
        "{}_{:x}",
        tcx.opt_item_name(did)
            .or_else(|| {
                use hir::def::DefKind::*;
                match tcx.def_kind(did) {
                    OpaqueTy => Some(Symbol::intern("opaque")),
                    _ => None
                }
            })
            .unwrap_or_else(|| panic!("Could not name {} {:?}", tcx.def_path_debug_str(did), tcx.def_kind(did))),
        short_hash_pls(did),
    ))
}

/// Extension trait for [`TyCtxt`]
pub trait TyCtxtExt<'tcx> {
    /// Resolve this [`BodyId`] to its actual body. Returns
    /// [`BodyWithBorrowckFacts`](crate::rust::rustc_borrowck::BodyWithBorrowckFacts),
    /// because it internally uses flowistry's body resolution
    /// ([`flowistry::mir::borrowck_facts::get_body_with_borrowck_facts`]) which
    /// memoizes its results so this is actually a cheap query.
    fn body_for_body_id(
        self,
        b: BodyId,
    ) -> &'tcx flowistry::mir::borrowck_facts::CachedSimplifedBodyWithFacts<'tcx>;
}

impl<'tcx> TyCtxtExt<'tcx> for TyCtxt<'tcx> {
    fn body_for_body_id(
        self,
        b: BodyId,
    ) -> &'tcx flowistry::mir::borrowck_facts::CachedSimplifedBodyWithFacts<'tcx> {
        flowistry::mir::borrowck_facts::get_body_with_borrowck_facts(
            self,
            self.hir().body_owner_def_id(b),
        )
    }
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

type SparseMatrixImpl<K, V> = FxHashMap<K, FxHashSet<V>>;

#[derive(Debug, Clone)]
pub struct SparseMatrix<K, V> {
    matrix: SparseMatrixImpl<K, V>,
    empty_set: FxHashSet<V>,
}

impl<'a, Q: Eq + std::hash::Hash + ?Sized, K: Eq + std::hash::Hash + std::borrow::Borrow<Q>, V>
    std::ops::Index<&'a Q> for SparseMatrix<K, V>
{
    type Output = <SparseMatrixImpl<K, V> as std::ops::Index<&'a Q>>::Output;
    fn index(&self, index: &Q) -> &Self::Output {
        &self.matrix[index]
    }
}

impl<K, V> Default for SparseMatrix<K, V> {
    fn default() -> Self {
        Self {
            matrix: Default::default(),
            empty_set: Default::default(),
        }
    }
}

impl<K: Eq + std::hash::Hash, V: Eq + std::hash::Hash> PartialEq for SparseMatrix<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.matrix.eq(&other.matrix)
    }
}
impl<K: Eq + std::hash::Hash, V: Eq + std::hash::Hash> Eq for SparseMatrix<K, V> {}

impl<K, V> SparseMatrix<K, V> {
    pub fn set(&mut self, k: K, v: V) -> bool
    where
        K: Eq + std::hash::Hash,
        V: Eq + std::hash::Hash,
    {
        self.row_mut(k).insert(v)
    }

    pub fn rows(&self) -> impl Iterator<Item = (&K, &FxHashSet<V>)> {
        self.matrix.iter()
    }

    pub fn row(&self, k: &K) -> &FxHashSet<V>
    where
        K: Eq + std::hash::Hash,
    {
        self.matrix.get(k).unwrap_or(&self.empty_set)
    }

    pub fn row_mut(&mut self, k: K) -> &mut FxHashSet<V>
    where
        K: Eq + std::hash::Hash,
    {
        self.matrix.entry(k).or_insert_with(HashSet::default)
    }

    pub fn has(&self, k: &K) -> bool
    where
        K: Eq + std::hash::Hash,
    {
        !self.matrix.get(k).map_or(true, HashSet::is_empty)
    }

    pub fn union_row(&mut self, k: &K, row: Cow<FxHashSet<V>>) -> bool
    where
        K: Eq + std::hash::Hash + Clone,
        V: Eq + std::hash::Hash + Clone,
    {
        let mut changed = false;
        if !self.has(k) {
            changed = !row.is_empty();
            self.matrix.insert(k.clone(), row.into_owned());
        } else {
            let set = self.row_mut(k.clone());
            row.iter()
                .for_each(|elem| changed |= set.insert(elem.clone()));
        }
        changed
    }
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
