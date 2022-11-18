//! Utility functions, general purpose structs and extension traits

use crate::{
    desc::Identifier,
    rust::{
        ast, hir,
        hir::{def_id::DefId, hir_id::HirId, BodyId},
        mir::{self, Location, Place, Statement, Terminator},
        rustc_span::symbol::Ident,
        ty,
    },
    Either, HashSet, Symbol, TyCtxt,
};

/// This is meant as an extension trait for `ast::Attribute`. The main method of
/// interest is [`match_extract`](#tymethod.match_extract),
/// [`matches_path`](#method.matches_path) is interesting if you want to check
/// if this attribute has the pat of interest but you do not care about its
/// payload.
pub trait MetaItemMatch {
    /// If the provided symbol path matches the path segments in the attribute
    /// *exactly* then this method applies the parse function and returns the
    /// results of parsing. Otherwise returns `None`.
    /// 
    /// For constructing parsers for `F` consider the [`ann_parse`](../ann_parse/index.html) module.
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

/// Extract a `DefId` if this type references an object that has one. This is
/// true for most user defined types, including types form the standard library,
/// but not builtin types, such as `u32`, arrays or ad-hoc types such as
/// function pointers.
///
/// Use with caution, this function might not be exhaustive (yet).
pub fn ty_def(ty: ty::Ty) -> Option<DefId> {
    match ty.kind() {
        ty::TyKind::Adt(def, _) => Some(def.did()),
        ty::TyKind::Foreign(did)
        | ty::TyKind::FnDef(did, _)
        | ty::TyKind::Closure(did, _)
        | ty::TyKind::Generator(did, _, _)
        | ty::TyKind::Opaque(did, _) => Some(*did),
        _ => None,
    }
}

/// Generic arguments can reference non-type things (in particular constants and
/// lifetimes). If it is a type, then this extracts that type, otherwise `None`.
pub fn generic_arg_as_type(a: ty::subst::GenericArg) -> Option<ty::Ty> {
    match a.unpack() {
        ty::subst::GenericArgKind::Type(t) => Some(t),
        _ => None,
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
        &'static str,
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
        &'static str,
    > {
        self.kind.as_fn_and_args()
    }
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
        &'static str,
    > {
        match self {
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                let defid = match func.constant().ok_or("Not a constant")? {
                    mir::Constant {
                        literal: mir::ConstantKind::Val(_, ty),
                        ..
                    } => match ty.kind() {
                        ty::FnDef(defid, _) | ty::Closure(defid, _) => Ok(*defid),
                        _ => Err("Not function type"),
                    },
                    _ => Err("Not value level constant"),
                }?;
                Ok((
                    defid,
                    args.iter()
                        .map(|a| match a {
                            mir::Operand::Move(p) | mir::Operand::Copy(p) => Some(*p),
                            mir::Operand::Constant(_) => None,
                        })
                        .collect(),
                    *destination,
                ))
            }
            _ => Err("Not a function call".into()),
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

/// This function deals with the fact that flowistry uses special locations to
/// refer to function arguments. Those locations are not recognized the rustc
/// functions that operate on MIR and thus need to be filtered before doing
/// things such as indexing into a `mir::Body`.
pub fn is_real_location(body: &mir::Body, l: mir::Location) -> bool {
    body.basic_blocks().get(l.block).map(|bb| 
            // Its `<=` because if len == statement_index it refers to the
            // terminator
            // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.Location.html
            l.statement_index <= bb.statements.len())
        == Some(true)
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
    places_read(l, stmt)
        .into_iter()
        .flat_map(move |place| provenance_of(tcx, place).into_iter())
}

/// Constructs a set of places that are ref/deref/field un-layerings of the input place.
pub fn provenance_of<'tcx>(tcx: TyCtxt<'tcx>, place: Place<'tcx>) -> Vec<Place<'tcx>> {
    use flowistry::mir::utils::PlaceExt;
    std::iter::once(place)
        .chain(
            place
                .refs_in_projection()
                .into_iter()
                .map(|t| mir::Place::from_ref(t.0, tcx)),
        )
        .collect()
}

pub fn node_as_fn<'hir>(
    node: &hir::Node<'hir>,
) -> Option<(&'hir Ident, &'hir hir::def_id::LocalDefId, &'hir BodyId)> {
    if let hir::Node::Item(hir::Item {
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
    }) = node
    {
        Some((ident, def_id, body_id))
    } else {
        None
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
    match body.stmt_at(l) {
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

/// Get the name of the function for this body as an `Ident`.
pub fn body_name_pls(tcx: TyCtxt, body_id: BodyId) -> Ident {
    tcx.hir()
        .find_by_def_id(tcx.hir().body_owner_def_id(body_id))
        .unwrap()
        .ident()
        .expect("no def id?")
}

/// Just give me a file that I can write to. (and overwrite)
pub fn outfile_pls<P: AsRef<std::path::Path>>(path: P) -> std::io::Result<std::fs::File> {
    std::fs::OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .open(path)
}

/// Return all places mentioned at this location that are *read*. Which means
/// that if a `Place` is not read but assigned (e.g. the return place of a
/// function call), it will not be in the result set.
pub fn places_read<'tcx>(
    location: mir::Location,
    stmt: &Either<&mir::Statement<'tcx>, &mir::Terminator<'tcx>>,
) -> impl Iterator<Item = mir::Place<'tcx>> {
    use mir::visit::Visitor;
    let mut places = HashSet::new();
    let mut vis = PlaceVisitor(|p: &mir::Place<'tcx>| {
        places.insert(*p);
    });
    match stmt {
        Either::Left(mir::Statement {
            kind: mir::StatementKind::Assign(a),
            ..
        }) => vis.visit_rvalue(&a.1, location),
        Either::Right(term) => vis.visit_terminator(term, location), // TODO this is not correct
        _ => (),
    };
    places.into_iter()
}

pub fn identifier_for_hid<'tcx>(tcx: TyCtxt<'tcx>, hid: HirId) -> Identifier {
    Identifier::new(tcx.item_name(tcx.hir().local_def_id(hid).to_def_id()))
}

pub fn identifier_for_fn<'tcx>(tcx: TyCtxt<'tcx>, p: DefId) -> Identifier {
    Identifier::new(tcx.item_name(p))
}

pub trait TyCtxtExt<'tcx> {
    fn body_for_body_id(
        self,
        b: BodyId,
    ) -> &'tcx crate::rust::rustc_borrowck::BodyWithBorrowckFacts<'tcx>;
}

impl<'tcx> TyCtxtExt<'tcx> for TyCtxt<'tcx> {
    fn body_for_body_id(
        self,
        b: BodyId,
    ) -> &'tcx crate::rust::rustc_borrowck::BodyWithBorrowckFacts<'tcx> {
        flowistry::mir::borrowck_facts::get_body_with_borrowck_facts(
            self,
            self.hir().body_owner_def_id(b),
        )
    }
}

/// A simple utility type that lets you split off a part of a struct and operate
/// on it separately while being assured that as soon as the `Split` goes out of
/// scope the separate part is merged back onto the main struct.
///
/// The [`Splittable`](./trait.Splittable.html) trait governs which part is the
/// main one and which is the split.
/// [`split()`](./trait.Splittable.html#method.split) is called on construction
/// and [`merge()`](./trait.Splittable.html#method.merge) when this struct goes
/// out of scope.
///
/// You can construct a `Split` easily using `into()`.
/// 
/// ## Usage
/// 
/// Usually you would construct the `Split` using `into()`, then obtain the two
/// contained parts with [`as_components`](#method.as_components). At the end of
/// the scope the split-off component is merged back automatically into the main
/// type in the `Drop` implementation for `Split`.
pub struct Split<'a, T: Splittable> {
    main: &'a mut T,
    inner: std::mem::MaybeUninit<T::Splitted>,
}

impl <'a, T:Splittable> Split<'a, T> {
    /// Obtain a mutable reference to both the main type and it's split-off part
    pub fn as_components(&mut self) -> (&mut T, &mut T::Splitted) {
        (self.main, unsafe { self.inner.assume_init_mut() })
    }
}

/// A type where a part of it can be moved out and merged back in. Usually this
/// would be implemented by having a field on `Self` that is
/// `Option<Self::Splitted>` or `MaybeUninit<Self::Splitted>`. For an example
/// see
/// [`FunctionInliner`](../ana/struct.FunctionInliner.html#structfield.under_construction)
pub trait Splittable: Sized {
    type Splitted;
    /// Move a part of this type out so it can be accessed independently.
    fn split(&mut self) -> Self::Splitted;
    /// Merge the moved-out part back into `self`
    fn merge(&mut self, inner: Self::Splitted);
}

impl<'a, T: Splittable> From<&'a mut T> for Split<'a, T> {
    fn from(main: &'a mut T) -> Self {
        let inner = std::mem::MaybeUninit::new(main.split());
        Split { main, inner }
    }
}

impl<'a, T: Splittable> Drop for Split<'a, T> {
    fn drop(&mut self) {
        let inner_moved = std::mem::replace(&mut self.inner, std::mem::MaybeUninit::uninit());
        self.main.merge(unsafe { inner_moved.assume_init() });
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

