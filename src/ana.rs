use std::{borrow::Cow, cell::RefCell, rc::Rc};

use crate::{
    dbg::{self},
    desc::*,
    rust::*,
    sah::HashVerifications,
    serializers, Either, HashMap, HashSet,
};

use hir::{
    def_id::DefId,
    hir_id::HirId,
    intravisit::{self, FnKind},
    BodyId,
};
use rustc_data_structures::{intern::Interned, sharded::ShardedHashMap};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    hir::nested_filter::OnlyBodies,
    mir::TerminatorKind,
    ty::{self, TyCtxt},
};
use rustc_span::{symbol::Ident, Span, Symbol};

use crate::rust::rustc_arena;
use flowistry::{
    indexed::{impls::LocationDomain, IndexedDomain},
    infoflow::{self, FlowAnalysis, FlowDomain, NonTransitiveFlowDomain},
    mir::{borrowck_facts, engine::AnalysisResults, utils::BodyExt},
};

pub type AttrMatchT = Vec<Symbol>;

trait MetaItemMatch {
    fn match_extract<A, F: Fn(&ast::MacArgs) -> A>(&self, p: &[Symbol], f: F) -> Option<A>;
    fn matches_path(&self, p: &[Symbol]) -> bool {
        self.match_extract(p, |_| ()).is_some()
    }
}

impl MetaItemMatch for ast::Attribute {
    fn match_extract<A, F: Fn(&ast::MacArgs) -> A>(&self, p: &[Symbol], f: F) -> Option<A> {
        match &self.kind {
            rustc_ast::ast::AttrKind::Normal(ast::AttrItem { path, args, .. }, _)
                if path.segments.len() == p.len()
                    && path
                        .segments
                        .iter()
                        .zip(p)
                        .all(|(seg, i)| seg.ident.name == *i) =>
            {
                Some(f(args))
            }
            _ => None,
        }
    }
}

fn ty_def(ty: ty::Ty) -> Option<DefId> {
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

fn generic_arg_as_type(a: ty::subst::GenericArg) -> Option<ty::Ty> {
    match a.unpack() {
        ty::subst::GenericArgKind::Type(t) => Some(t),
        _ => None,
    }
}

trait TerminatorExt<'tcx> {
    fn as_fn_and_args(
        &self,
    ) -> Result<
        (
            DefId,
            Vec<Option<mir::Place<'tcx>>>,
            Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        ),
        &'static str,
    >;
}

impl<'tcx> TerminatorExt<'tcx> for mir::Terminator<'tcx> {
    fn as_fn_and_args(
        &self,
    ) -> Result<
        (
            DefId,
            Vec<Option<mir::Place<'tcx>>>,
            Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        ),
        &'static str,
    > {
        match &self.kind {
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
/// object via the visit::Visitor` trait. Usually used to accumulate information
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

pub struct Visitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    opts: &'static crate::Args,
    marked_objects: HashMap<HirId, (Vec<Annotation>, ObjectType)>,
    marked_stmts: HashMap<HirId, ((Vec<Annotation>, usize), Span, DefId)>,
    functions_to_analyze: Vec<(Ident, BodyId, &'tcx rustc_hir::FnDecl<'tcx>)>,
}

type CallSiteAnnotations = HashMap<DefId, (Vec<Annotation>, usize)>;

pub struct Flow<'tcx, 'g> {
    pub root_function: BodyId,
    pub function_flows: FunctionFlows<'tcx, 'g>,
    pub reduced_flow: CallOnlyFlow<'g>,
}

/// The idea of a global location is to capture the call chain up to a specific
/// location. The type is organized from the outside in i.e. the top-level
/// function call is the outermost location which calls `next` at `location`
/// going one level deeper and so forth. You may access the innermost location
/// using `GlobalLocation::innermost_location_and_body`.
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub struct GlobalLocation<'g>(Interned<'g, GlobalLocationS<GlobalLocation<'g>>>);

pub trait IsGlobalLocation: Sized {
    fn as_global_location_s(&self) -> &GlobalLocationS<Self>;
    fn function(&self) -> BodyId {
        self.as_global_location_s().function
    }
    fn location(&self) -> mir::Location {
        self.as_global_location_s().location
    }
    fn next(&self) -> Option<&Self> {
        self.as_global_location_s().next.as_ref()
    }
    fn innermost_location_and_body(&self) -> (mir::Location, BodyId) {
        self.next().map_or_else(
            || (self.location(), self.function()),
            |other| other.innermost_location_and_body(),
        )
    }
    fn as_local(self) -> Option<mir::Location> {
        if self.next().is_none() {
            Some(self.location())
        } else {
            None
        }
    }
    fn is_at_root(self) -> bool {
        self.next().is_none()
    }
}

impl<'g> IsGlobalLocation for GlobalLocation<'g> {
    fn as_global_location_s(&self) -> &GlobalLocationS<Self> {
        self.0 .0
    }
}

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
/// the interned wrapper type `GlobalLocation<'g>, which gives access to the
/// same fields with methods such as `function()`, `location()` and `next()`.
///
/// Other methods and general information for global locations is documented on
/// the `GlobalLocation<'g>`.
///
/// The generic parameter `Inner` is typically instantiated recursively with the
/// interned wrapper type `GlobalLocation<'g>`, forming an interned linked list.
/// We use a generic parameter so that deserializers can instead instantiate
/// them as `GlobalLocationS`, i.e. a non-interned version of the same struct.
/// This is necessary because in the derived deserializers we do not have access
/// to the interner.
#[derive(PartialEq, Eq, Hash, Debug, Clone, serde::Deserialize, serde::Serialize)]
pub struct GlobalLocationS<Inner> {
    #[serde(with = "crate::serializers::BodyIdProxy")]
    pub function: BodyId,
    #[serde(with = "crate::serializers::ser_loc")]
    pub location: mir::Location,
    pub next: Option<Inner>,
}

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
    pub fn globalize_location(
        self,
        location: mir::Location,
        function: BodyId,
    ) -> GlobalLocation<'g> {
        self.make_global_location(function, location, None)
    }
    pub fn global_location_from_relative(
        self,
        relative_location: GlobalLocation<'g>,
        root_location: mir::Location,
        root_function: BodyId,
    ) -> GlobalLocation<'g> {
        self.make_global_location(root_function, root_location, Some(relative_location))
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub struct GlobalPlace<'tcx, Location> {
    pub place: mir::Place<'tcx>,
    pub function: Option<Location>,
}

impl<'tcx, 'g> GlobalPlace<'tcx, GlobalLocation<'g>> {
    pub fn relative_to(
        mut self,
        gli: GLI<'g>,
        root_location: mir::Location,
        root_function: BodyId,
    ) -> Self {
        self.function = Some(gli.make_global_location(root_function, root_location, self.function));
        self
    }
}

impl<'tcx, 'g, Location> From<mir::Place<'tcx>> for GlobalPlace<'tcx, Location> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Self {
            place,
            function: None,
        }
    }
}

type GlobalDepMatrix<'tcx, 'g> =
    HashMap<GlobalPlace<'tcx, GlobalLocation<'g>>, HashSet<GlobalLocation<'g>>>;
pub struct GlobalFlowGraph<'tcx, 'g> {
    location_states: HashMap<GlobalLocation<'g>, GlobalDepMatrix<'tcx, 'g>>,
    return_state: GlobalDepMatrix<'tcx, 'g>,
}
type FunctionFlows<'tcx, 'g> = RefCell<HashMap<BodyId, Option<Rc<GlobalFlowGraph<'tcx, 'g>>>>>;
pub type CallOnlyFlow<'g> = HashMap<GlobalLocation<'g>, CallDeps<GlobalLocation<'g>>>;

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(bound(
    serialize = "Location: std::cmp::Eq + std::hash::Hash + serde::Serialize",
    deserialize = "Location: std::cmp::Eq + std::hash::Hash + serde::Deserialize<'de>"
))]
pub struct CallDeps<Location> {
    pub ctrl_deps: HashSet<Location>,
    pub input_deps: Vec<HashSet<Location>>,
}

fn inner_flow_for_terminator<'tcx, 'g, P: Fn(LocalDefId) -> bool + Copy>(
    tcx: TyCtxt<'tcx>,
    gli: GLI<'g>,
    function_flows: &FunctionFlows<'tcx, 'g>,
    t: &mir::Terminator<'tcx>,
    inline_selector: P,
) -> Result<
    (
        Rc<GlobalFlowGraph<'tcx, 'g>>,
        BodyId,
        &'tcx mir::Body<'tcx>,
        Vec<Option<mir::Place<'tcx>>>,
        Option<(mir::Place<'tcx>, mir::BasicBlock)>,
    ),
    &'static str,
> {
    debug!("Considering {:?}", t);
    t.as_fn_and_args().and_then(|(p, args, dest)| {
        let node = tcx.hir().get_if_local(p).ok_or("non-local node")?;
        let (callee_id, callee_local_id, callee_body_id) = node_as_fn(&node)
            .unwrap_or_else(|| panic!("Expected local function node, got {node:?}"));
        let () = if inline_selector(*callee_local_id) {
            debug!("Selector succeeded.");
            Ok(())
        } else {
            debug!("Selector failed");
            Err("Inline selector was false")
        }?;
        let inner_flow = compute_granular_global_flows(
            tcx,
            gli,
            *callee_body_id,
            function_flows,
            inline_selector,
        )
        .ok_or("is recursive")?;
        let body = &borrowck_facts::get_body_with_borrowck_facts(tcx, *callee_local_id).body;
        debug!("Inner flow computed");
        Ok((inner_flow, *callee_body_id, body, args, dest))
    })
}

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
    use mir::{Place, ProjectionElem};
    if child.local == mir::RETURN_PLACE && child.projection.len() == 0 {
        debug!("Child is return place");
        if child.ty(body.local_decls(), tcx).ty.is_unit() {
            return None;
        }

        if let Some((dst, _)) = destination {
            debug!("Returning destination");
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

fn compute_granular_global_flows<'tcx, 'g, P: Fn(LocalDefId) -> bool + Copy>(
    tcx: TyCtxt<'tcx>,
    gli: GLI<'g>,
    root_function: BodyId,
    function_flows: &FunctionFlows<'tcx, 'g>,
    inline_selector: P,
) -> Option<Rc<GlobalFlowGraph<'tcx, 'g>>> {
    if let Some(inner) = function_flows.borrow().get(&root_function) {
        return inner.clone();
    };
    let local_def_id = tcx.hir().body_owner_def_id(root_function);

    let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, local_def_id);
    let body = &body_with_facts.body;
    let ref from_flowistry =
        flowistry::infoflow::compute_flow_nontransitive(tcx, root_function, body_with_facts);

    // Make sure we terminate on recursion
    function_flows.borrow_mut().insert(root_function, None);

    let mut translated_return_states: RefCell<
        HashMap<mir::Location, HashMap<mir::Place<'tcx>, HashSet<GlobalLocation<'g>>>>,
    > = RefCell::new(HashMap::new());
    let make_row_global = |place, dep_set: IndexSet<_, _>| -> HashSet<GlobalLocation<'g>> {
        dep_set
            .iter()
            .flat_map(|l| {
                if let Some((t, (inner_flow, _, inner_body, args, dest))) =
                    if !is_real_location(body, *l) {
                        None
                    } else {
                        body.stmt_at(*l).right().and_then(|t| {
                            Some((
                                t,
                                inner_flow_for_terminator(
                                    tcx,
                                    gli,
                                    function_flows,
                                    t,
                                    inline_selector,
                                )
                                .ok()?,
                            ))
                        })
                    }
                {
                    debug!("Inspecting inner flow for {:?}", t.kind);
                    let mut translated_return_states_borrow = translated_return_states.borrow_mut();
                    let translated_return_state = translated_return_states_borrow
                        .entry(*l)
                        .or_insert_with(|| {
                            debug!(
                                "Translating return state with dependency set of size {}",
                                inner_flow.return_state.len()
                            );
                            inner_flow
                                .return_state
                                .iter()
                                .filter_map(|(p, deps)| {
                                    if p.function.is_none() {
                                        let parent = translate_child_to_parent(
                                            tcx,
                                            local_def_id,
                                            &args,
                                            dest,
                                            p.place,
                                            true,
                                            inner_body,
                                            body,
                                        );
                                        if parent.is_none() {
                                            debug!(
                                                "No parent found for {:?} (dest is {}present)",
                                                p.place,
                                                if dest.is_none() { "not " } else { "" }
                                            );
                                        }
                                        parent
                                    } else {
                                        None
                                    }
                                    .map(|parent| {
                                        (
                                            parent,
                                            deps.iter()
                                                .map(|d| {
                                                    gli.global_location_from_relative(
                                                        *d,
                                                        *l,
                                                        root_function,
                                                    )
                                                })
                                                .collect(),
                                        )
                                    })
                                })
                                .collect()
                        });
                    if let Some(deps) = translated_return_state.get(&place) {
                        deps.iter().cloned().collect::<Vec<_>>()
                    } else {
                        warn!(
                            "Dependent place {:?} not found in translated return states {:?}",
                            place, translated_return_state
                        );
                        vec![]
                    }
                } else {
                    vec![gli.make_global_location(root_function, *l, None)]
                }
                .into_iter()
            })
            .collect()
    };
    // What to do for locations that are non-inlineable calls
    let handle_regular_location = |loc| {
        from_flowistry
            .state_at(loc)
            .matrix()
            .rows()
            .map(|(place, dep_set)| {
                (
                    GlobalPlace {
                        place,
                        function: None,
                    },
                    make_row_global(place, dep_set),
                )
            })
            .collect::<HashMap<_, _>>()
    };
    let mut return_state: HashMap<GlobalPlace<'tcx, _>, HashSet<GlobalLocation<'g>>> =
        HashMap::new();
    let location_states = body_with_facts
        .body
        .basic_blocks()
        .iter_enumerated()
        .flat_map(|(bb, bbdat)| {
            bbdat
                .statements
                .iter()
                .enumerate()
                .map(move |(idx, stmt)| {
                    let loc = mir::Location {
                        block: bb,
                        statement_index: idx,
                    };
                    let global_loc = gli.make_global_location(root_function, loc, None);
                    (global_loc, handle_regular_location(loc))
                })
                .chain({
                    let loc = body.terminator_loc(bb);
                    if let Ok((inner_flow, inner_body_id, inner_body, args, dest)) =
                        inner_flow_for_terminator(
                            tcx,
                            gli,
                            function_flows,
                            bbdat.terminator(),
                            inline_selector,
                        )
                    {
                        let global_terminator_loc = gli.globalize_location(loc, inner_body_id);
                        let caller_state = from_flowistry.state_at(loc).matrix();
                        let as_parent_dep_matrix: GlobalDepMatrix<'tcx, 'g> = inner_flow
                            .location_states
                            .values()
                            .flat_map(|s| s.keys())
                            .filter(|gp| gp.function.is_none())
                            .map(|gp| gp.place)
                            .collect::<HashSet<_>>()
                            .into_iter()
                            .filter_map(|p| {
                                Some((
                                    p,
                                    translate_child_to_parent(
                                        tcx,
                                        local_def_id,
                                        &args,
                                        dest,
                                        p,
                                        false,
                                        inner_body,
                                        body,
                                    )?,
                                ))
                            })
                            .map(|(child, parent)| {
                                (
                                    GlobalPlace {
                                        place: child,
                                        function: Some(global_terminator_loc),
                                    },
                                    make_row_global(parent, caller_state.row_set(parent)),
                                )
                            })
                            .collect();

                        inner_flow
                            .location_states
                            .iter()
                            .map(move |(inner_loc, map)| {
                                (
                                    gli.global_location_from_relative(
                                        *inner_loc,
                                        loc,
                                        root_function,
                                    ),
                                    map.iter()
                                        .map(|(place, deps)| {
                                            (
                                                place.relative_to(gli, loc, root_function),
                                                deps.iter()
                                                    .map(|dep| {
                                                        gli.global_location_from_relative(
                                                            *dep,
                                                            loc,
                                                            root_function,
                                                        )
                                                    })
                                                    .collect::<HashSet<_>>(),
                                            )
                                        })
                                        .collect::<HashMap<_, _>>(),
                                )
                            })
                            .chain((1..=args.len()).into_iter().map(move |a| {
                                let global_call_site = gli.globalize_location(
                                    mir::Location {
                                        block: mir::BasicBlock::from_usize(
                                            inner_body.basic_blocks().len(),
                                        ),
                                        statement_index: a,
                                    },
                                    inner_body_id,
                                );
                                let global_arg_loc = gli.global_location_from_relative(
                                    global_call_site,
                                    loc,
                                    root_function,
                                );
                                (global_arg_loc, as_parent_dep_matrix.clone())
                            }))
                            .collect()
                    } else {
                        let state_at_term = handle_regular_location(loc);
                        if let TerminatorKind::Return = bbdat.terminator().kind {
                            for (p, deps) in state_at_term.iter() {
                                return_state
                                    .entry(*p)
                                    .or_insert_with(|| HashSet::new())
                                    .extend(deps.iter().cloned());
                            }
                        };
                        vec![(gli.globalize_location(loc, root_function), state_at_term)]
                    }
                    .into_iter()
                })
        })
        .collect();
    function_flows.borrow_mut().insert(
        root_function,
        Some(Rc::new(GlobalFlowGraph {
            location_states,
            return_state,
        })),
    );
    Some(
        function_flows.borrow()[&root_function]
            .as_ref()
            .unwrap()
            .clone(),
    )
}

fn compute_call_only_flow<'tcx, 'g>(
    tcx: TyCtxt<'tcx>,
    g: &GlobalFlowGraph<'tcx, 'g>,
) -> CallOnlyFlow<'g> {
    // I'm making these generic so I don't have to update the types inside all the time and can use inference instead.
    enum Keep<OnKeep, OnReject> {
        Keep(OnKeep),
        Argument(usize),
        Reject(OnReject),
    }
    let as_location_to_keep = |loc: GlobalLocation| {
        let (inner_location, inner_body_id) = loc.innermost_location_and_body();
        let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(
            tcx,
            tcx.hir().body_owner_def_id(inner_body_id),
        );
        if !is_real_location(&body_with_facts.body, inner_location) || loc.next().is_none() {
            Keep::Argument(inner_location.statement_index)
        } else {
            let stmt_at_loc = body_with_facts.body.stmt_at(inner_location);
            match stmt_at_loc {
                Either::Right(t) => t
                    .as_fn_and_args()
                    .ok()
                    .map_or(Keep::Reject(stmt_at_loc), |(_, args, dest)| {
                        Keep::Keep((args, dest))
                    }),
                _ => Keep::Reject(stmt_at_loc),
            }
        }
    };
    g.location_states
        .iter()
        .filter_map(|(loc, place_deps)| {
            let (args, dest) = match as_location_to_keep(*loc) {
                Keep::Keep(k) => Some(k),
                _ => None,
            }?;
            let deps_for = |p: mir::Place| {
                let place_as_global = GlobalPlace {
                    place: p,
                    function: loc.next().cloned(),
                };
                let place_dep_row = place_deps.get(&place_as_global);
                if place_dep_row.is_none() {
                    warn!("No dependencies found for place {:?}", place_as_global);
                }

                let mut queue = place_dep_row
                    .into_iter()
                    .flat_map(|f| f.iter())
                    .cloned()
                    .collect::<Vec<_>>();
                let mut seen = HashSet::new();
                let mut deps = HashSet::new();
                while let Some(p) = queue.pop() {
                    match as_location_to_keep(p) {
                        Keep::Keep(_) | Keep::Argument(_) => {
                            deps.insert(p);
                        }
                        Keep::Reject(stmt_at_loc) if !seen.contains(&p) => {
                            seen.insert(p);
                            queue.extend(
                                read_places_with_provenance(loc.location(), &stmt_at_loc, tcx)
                                    .flat_map(|pl| {
                                        place_deps[&GlobalPlace {
                                            place: pl,
                                            function: p.next().cloned(),
                                        }]
                                            .iter()
                                            .cloned()
                                    }),
                            )
                        }
                        _ => (),
                    }
                }
                deps
            };
            dest.map(|(dest, _)| {
                (
                    *loc,
                    CallDeps {
                        input_deps: args
                            .into_iter()
                            .map(|p| p.map_or_else(|| HashSet::new(), deps_for))
                            .collect(),
                        ctrl_deps: deps_for(dest),
                    },
                )
            })
        })
        .collect()
}

fn places_read<'tcx>(
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

impl<'tcx, 'g> Flow<'tcx, 'g> {
    fn compute<P: Fn(LocalDefId) -> bool + Copy>(
        opts: &crate::AnalysisCtrl,
        tcx: TyCtxt<'tcx>,
        body_id: BodyId,
        gli: GLI<'g>,
        inline_selector: P,
    ) -> Self {
        let mut eval_mode = flowistry::extensions::EvalMode::default();
        let mut function_flows = RefCell::new(HashMap::new());
        eval_mode.context_mode = flowistry::extensions::ContextMode::Recurse;
        let reduced_flow = flowistry::extensions::EVAL_MODE.set(&eval_mode, || {
            compute_call_only_flow(
                tcx,
                &compute_granular_global_flows(tcx, gli, body_id, &function_flows, inline_selector)
                    .unwrap(),
            )
        });
        Self {
            root_function: body_id,
            function_flows: function_flows,
            reduced_flow,
        }
    }
}

pub fn read_places_with_provenance<'tcx>(
    l: mir::Location,
    stmt: &Either<&mir::Statement<'tcx>, &mir::Terminator<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> impl Iterator<Item = mir::Place<'tcx>> {
    use flowistry::mir::utils::PlaceExt;
    places_read(l, stmt).into_iter().flat_map(move |place| {
        std::iter::once(place)
            .chain(
                place
                    .refs_in_projection()
                    .into_iter()
                    .map(|t| mir::Place::from_ref(t.0, tcx)),
            )
            .collect::<Vec<_>>()
            .into_iter()
    })
}

fn node_as_fn<'hir>(
    node: &hir::Node<'hir>,
) -> Option<(&'hir Ident, &'hir hir::def_id::LocalDefId, &'hir BodyId)> {
    if let hir::Node::Item(hir::Item {
        ident,
        def_id,
        kind: hir::ItemKind::Fn(_, _, body_id),
        ..
    }) = node
    {
        Some((ident, def_id, body_id))
    } else {
        None
    }
}

pub fn outfile_pls<P: AsRef<std::path::Path>>(path: P) -> std::io::Result<std::fs::File> {
    std::fs::OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .open(path)
}

impl<'tcx> Visitor<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, opts: &'static crate::Args) -> Self {
        Self {
            tcx,
            opts,
            marked_objects: HashMap::new(),
            marked_stmts: HashMap::new(),
            functions_to_analyze: vec![],
        }
    }

    fn should_analyze_function(&self, ident: HirId) -> bool {
        self.tcx
            .hir()
            .attrs(ident)
            .iter()
            .any(|a| a.matches_path(&crate::ANALYZE_MARKER))
    }

    pub fn run(mut self) -> std::io::Result<ProgramDescription> {
        let tcx = self.tcx;
        tcx.hir().deep_visit_all_item_likes(&mut self);
        //println!("{:?}\n{:?}\n{:?}", self.marked_sinks, self.marked_sources, self.functions_to_analyze);
        self.analyze()
    }

    fn annotated_subtypes(&self, ty: ty::Ty) -> HashSet<TypeDescriptor> {
        ty.walk()
            .filter_map(|ty| {
                generic_arg_as_type(ty)
                    .and_then(ty_def)
                    .and_then(DefId::as_local)
                    .and_then(|def| {
                        let hid = self.tcx.hir().local_def_id_to_hir_id(def);
                        if self.marked_objects.contains_key(&hid) {
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
    fn handle_target<'g>(
        &self,
        hash_verifications: &mut HashVerifications,
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
            // This is a bit ugly. This basically just cleans up the fact that
            // when we integrate an annotation on a call, its slightly
            // cumbersome to find out how many arguments the call has. So I just
            // fill in the largest annotated value and then have it merge here
            // later in case we know of more arguments.
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
        let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, local_def_id);

        if self.opts.dbg.dump_ctrl_mir {
            mir::graphviz::write_mir_fn_graphviz(
                tcx,
                &body_with_facts.body,
                false,
                &mut outfile_pls(format!("{}.mir.gv", id.name)).unwrap(),
            )
            .unwrap()
        }

        debug!("{}", id.name);
        let flow = Flow::compute(&self.opts.anactrl, tcx, b, gli, |did| {
            self.marked_objects
                .get(&tcx.hir().local_def_id_to_hir_id(did))
                .map_or(true, |anns| anns.0.is_empty())
        });

        let body = &body_with_facts.body;
        {
            let types = body.args_iter().map(|l| {
                let ty = body.local_decls[l].ty;
                let subtypes = self.annotated_subtypes(ty);
                (DataSource::Argument(l.as_usize() - 1), subtypes)
            });
            flows.add_types(types);
        }

        if self.opts.dbg.dump_flowistry_matrix {
            unimplemented!();
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

        let body_for_body_id =
            |b| borrowck_facts::get_body_with_borrowck_facts(tcx, tcx.hir().body_owner_def_id(b));
        let body_with_facts = body_for_body_id(b);
        let ref body = body_with_facts.body;

        for (loc, deps) in flow.reduced_flow.iter() {
            if !is_real_location(&body, loc.location()) {
                // These can only be (controller) arguments and they cannot have dependencies (and thus not receive any data)
                continue;
            }
            let (terminator, (defid, _, _)) = match body
                .stmt_at(loc.location())
                .right()
                .ok_or("not a terminator")
                .and_then(|t| Ok((t, t.as_fn_and_args()?)))
            {
                Ok(term) => term,
                Err(err) => {
                    warn!("Odd location in graph creation '{}'", err);
                    continue;
                }
            };
            let call_site = CallSite {
                called_from: Identifier::new(
                    tcx.hir()
                        .find_by_def_id(
                            tcx.hir()
                                .body_owner_def_id(loc.next().map_or(b, |f| f.function())),
                        )
                        .unwrap()
                        .ident()
                        .expect("no def id?")
                        .name,
                ),
                location: loc.location(),
                function: identifier_for_fn(tcx, defid),
            };
            let anns = interesting_fn_defs.get(&defid).map(|a| a.0.as_slice());

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
                unimplemented!();
                for ann in anns.iter().filter_map(Annotation::as_exception_annotation) {
                    //hash_verifications.handle(ann, tcx, terminator, &body, loc, matrix);
                }
                // TODO this is attaching to functions instead of call
                // sites. Once we start actually tracking call sites
                // this needs to be adjusted
                register_call_site(tcx, call_site_annotations, defid, Some(anns));
            }
            register_call_site(tcx, call_site_annotations, defid, anns);
            for (arg_slot, arg_deps) in deps.input_deps.iter().enumerate() {
                for dep in arg_deps.iter() {
                    flows.add(
                        Cow::Owned({
                            if loc.is_at_root() && !is_real_location(&body, dep.location()) {
                                DataSource::Argument(dep.location().statement_index - 1)
                            } else {
                                DataSource::FunctionCall(CallSite {
                                    called_from: Identifier::new(
                                        tcx.hir()
                                            .find_by_def_id(
                                                tcx.hir().body_owner_def_id(dep.function()),
                                            )
                                            .unwrap()
                                            .ident()
                                            .expect("no def id?")
                                            .name,
                                    ),
                                    location: dep.location(),
                                    function: identifier_for_fn(
                                        tcx,
                                        body_for_body_id(dep.function())
                                            .body
                                            .stmt_at(dep.location())
                                            .right()
                                            .expect("not a terminator")
                                            .as_fn_and_args()
                                            .unwrap()
                                            .0,
                                    ),
                                })
                            }
                        }),
                        if loc.is_at_root()
                            && matches!(
                                body.stmt_at(loc.location()),
                                Either::Right(mir::Terminator {
                                    kind: mir::TerminatorKind::Return,
                                    ..
                                })
                            )
                        {
                            DataSink::Return
                        } else {
                            DataSink::Argument {
                                function: call_site.clone(),
                                arg_slot,
                            }
                        },
                    );
                }
            }
        }
        Ok((Identifier::new(id.name), flows))
    }

    /// Main analysis driver
    fn analyze(mut self) -> std::io::Result<ProgramDescription> {
        let arena = rustc_arena::TypedArena::default();
        let interner = GlobalLocationInterner::new(&arena);
        let gli = GLI(&interner);
        let tcx = self.tcx;
        let mut targets = std::mem::replace(&mut self.functions_to_analyze, vec![]);
        let interesting_fn_defs = self
            .marked_objects
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

use flowistry::indexed::{IndexMatrix, IndexSet};

pub type NonTransitiveGraph<'tcx> =
    HashMap<mir::Location, IndexMatrix<mir::Place<'tcx>, mir::Location>>;

fn is_safe_function<'tcx>(_bound_sig: &ty::Binder<'tcx, ty::FnSig<'tcx>>) -> bool {
    return false;
}

fn identifier_for_hid<'tcx>(tcx: TyCtxt<'tcx>, hid: HirId) -> Identifier {
    Identifier::new(tcx.item_name(tcx.hir().local_def_id(hid).to_def_id()))
}

fn identifier_for_fn<'tcx>(tcx: TyCtxt<'tcx>, p: DefId) -> Identifier {
    Identifier::new(tcx.item_name(p))
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

impl<'tcx> intravisit::Visitor<'tcx> for Visitor<'tcx> {
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
