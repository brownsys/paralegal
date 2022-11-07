use std::{borrow::Cow, cell::RefCell, rc::Rc};

use crate::{
    dbg::{self, dump_non_transitive_graph_and_body},
    desc::*,
    rust::*,
    sah::HashVerifications,
    Either, HashMap, HashSet,
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

pub struct Flow<'a, 'tcx, 'g> {
    pub kind: FlowKind<'a, 'tcx, 'g>,
    pub domain: Rc<LocationDomain>,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub struct GlobalLocation<'g>(Interned<'g, GlobalLocationS<'g>>);

impl<'g> GlobalLocation<'g> {
    pub fn function(self) -> BodyId {
        self.0 .0.function
    }
    pub fn location(self) -> mir::Location {
        self.0 .0.location
    }
    pub fn next(self) -> Option<Self> {
        self.0 .0.next
    }
    pub fn innermost_location_and_body(self) -> (mir::Location, BodyId) {
        self.next().map_or_else(
            || (self.location(), self.function()),
            |other| other.innermost_location_and_body(),
        )
    }
    pub fn as_local(self) -> Option<mir::Location> {
        if self.next().is_none() {
            Some(self.location())
        } else {
            None
        }
    }
    pub fn is_at_root(self) -> bool {
        self.next().is_none()
    }
}

impl<'g> std::borrow::Borrow<GlobalLocationS<'g>> for GlobalLocation<'g> {
    fn borrow(&self) -> &GlobalLocationS<'g> {
        &self.0 .0
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct GlobalLocationS<'g> {
    pub function: BodyId,
    pub location: mir::Location,
    pub next: Option<GlobalLocation<'g>>,
}

pub struct GlobalLocationInterner<'g> {
    arena: &'g rustc_arena::TypedArena<GlobalLocationS<'g>>,
    known_locations: ShardedHashMap<GlobalLocation<'g>, ()>,
}

impl<'g> GlobalLocationInterner<'g> {
    pub fn intern_location(&'g self, loc: GlobalLocationS<'g>) -> GlobalLocation<'g> {
        self.known_locations.intern(loc, |loc| {
            GlobalLocation(Interned::new_unchecked(self.arena.alloc(loc)))
        })
    }
    pub fn new(arena: &'g rustc_arena::TypedArena<GlobalLocationS<'g>>) -> Self {
        GlobalLocationInterner {
            arena,
            known_locations: ShardedHashMap::default(),
        }
    }
}

#[derive(Clone, Copy)]
pub struct GLI<'g>(&'g GlobalLocationInterner<'g>);

impl<'g> GLI<'g> {
    pub fn make_global_location(
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
pub struct GlobalPlace<'tcx, 'g> {
    place: mir::Place<'tcx>,
    function: Option<GlobalLocation<'g>>,
}

impl<'tcx, 'g> GlobalPlace<'tcx, 'g> {
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

impl<'tcx, 'g> From<mir::Place<'tcx>> for GlobalPlace<'tcx, 'g> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Self {
            place,
            function: None,
        }
    }
}

type GlobalDepMatrix<'tcx, 'g> = HashMap<GlobalPlace<'tcx, 'g>, HashSet<GlobalLocation<'g>>>;
struct GlobalFlowGraph<'tcx, 'g> {
    location_states: HashMap<GlobalLocation<'g>, GlobalDepMatrix<'tcx, 'g>>,
    return_state: GlobalDepMatrix<'tcx, 'g>,
}
type FunctionFlows<'tcx, 'g> = RefCell<HashMap<BodyId, Option<Rc<GlobalFlowGraph<'tcx, 'g>>>>>;
type CallOnlyFlow<'g> = HashMap<GlobalLocation<'g>, CallDeps<'g>>;

struct CallDeps<'g> {
    ctrl_deps: HashSet<GlobalLocation<'g>>,
    input_deps: Vec<HashSet<GlobalLocation<'g>>>,
}

pub enum FlowKind<'a, 'tcx, 'g> {
    Transitive(
        flowistry::infoflow::FlowResults<'a, 'tcx, flowistry::infoflow::TransitiveFlowDomain<'tcx>>,
    ),
    NonTransitive(
        flowistry::infoflow::FlowResults<
            'a,
            'tcx,
            flowistry::infoflow::NonTransitiveFlowDomain<'tcx>,
        >,
    ),
    NonTransitiveShrunk {
        original_flow: flowistry::infoflow::FlowResults<
            'a,
            'tcx,
            flowistry::infoflow::NonTransitiveFlowDomain<'tcx>,
        >,
        shrunk: NonTransitiveGraph<'tcx>,
    },
    NonTransitiveRecursive {
        root_function: BodyId,
        function_flows: FunctionFlows<'tcx, 'g>,
        reduced_flow: CallOnlyFlow<'g>,
    },
}

fn inner_flow_for_terminator<'tcx, 'g>(
    tcx: TyCtxt<'tcx>,
    gli: GLI<'g>,
    function_flows: &FunctionFlows<'tcx, 'g>,
    t: &mir::Terminator<'tcx>,
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
    t.as_fn_and_args().and_then(|(p, args, dest)| {
        let node = tcx.hir().get_if_local(p).ok_or("non-local node")?;
        let (callee_id, callee_local_id, callee_body_id) = node_as_fn(&node)
            .unwrap_or_else(|| panic!("Expected local function node, got {node:?}"));
        let inner_flow = compute_granular_global_flows(tcx, gli, *callee_body_id, function_flows)
            .ok_or("is recursive")?;
        let body = &borrowck_facts::get_body_with_borrowck_facts(tcx, *callee_local_id).body;
        Ok((inner_flow, *callee_body_id, body, args, dest))
    })
}

fn compute_granular_global_flows<'tcx, 'g>(
    tcx: TyCtxt<'tcx>,
    gli: GLI<'g>,
    root_function: BodyId,
    function_flows: &FunctionFlows<'tcx, 'g>,
) -> Option<Rc<GlobalFlowGraph<'tcx, 'g>>> {
    if let Some(inner) = function_flows.borrow()[&root_function].as_ref() {
        return Some(inner.clone());
    };
    let local_def_id = tcx.hir().body_owner_def_id(root_function);

    let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, local_def_id);
    let body = &body_with_facts.body;
    let ref from_flowistry =
        flowistry::infoflow::compute_flow_nontransitive(tcx, root_function, body_with_facts);

    // Make sure we terminate on recursion
    function_flows.borrow_mut().insert(root_function, None);

    let translate_child_to_parent = |args: &[Option<mir::Place<'tcx>>],
                                     destination: Option<(mir::Place<'tcx>, _)>,
                                     child: mir::Place<'tcx>,
                                     mutated: bool|
     -> Option<mir::Place<'tcx>> {
        use flowistry::mir::utils::PlaceExt;
        use mir::HasLocalDecls;
        use mir::{Place, ProjectionElem};
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
        let mut ty = parent_toplevel_arg.ty(body.local_decls(), tcx);
        let parent_param_env = tcx.param_env(local_def_id);
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
    };

    let mut translated_return_states: RefCell<
        HashMap<mir::Location, HashMap<mir::Place<'tcx>, HashSet<GlobalLocation<'g>>>>,
    > = RefCell::new(HashMap::new());
    let make_row_global = |place, dep_set: IndexSet<_, _>| -> HashSet<GlobalLocation<'g>> {
        dep_set
            .iter()
            .flat_map(|l| {
                if let Some((inner_flow, _, inner_body, args, dest)) = body
                    .stmt_at(*l)
                    .right()
                    .and_then(|t| inner_flow_for_terminator(tcx, gli, function_flows, t).ok())
                {
                    let mut translated_return_states_borrow = translated_return_states.borrow_mut();
                    let translated_return_state = translated_return_states_borrow
                        .entry(*l)
                        .or_insert_with(|| {
                            inner_flow
                                .return_state
                                .iter()
                                .filter_map(|(p, deps)| {
                                    if p.function.is_none() {
                                        translate_child_to_parent(&args, dest, p.place, true)
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
                    translated_return_state[&place]
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
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
    let mut return_state: HashMap<GlobalPlace<'tcx, 'g>, HashSet<GlobalLocation<'g>>> =
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
                        inner_flow_for_terminator(tcx, gli, function_flows, bbdat.terminator())
                    {
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
                                (
                                    global_arg_loc,
                                    from_flowistry
                                        .state_at(loc)
                                        .matrix()
                                        .rows()
                                        .flat_map(|(place, dep_set)| {
                                            let global_terminator_loc =
                                                gli.globalize_location(loc, inner_body_id);
                                            let this_place_as_global = GlobalPlace {
                                                place,
                                                function: Some(global_terminator_loc),
                                            };
                                            let parent = translate_child_to_parent(
                                                &args, dest, place, false,
                                            );
                                            let row = make_row_global(place, dep_set);
                                            parent
                                                .map(|parent| {
                                                    (
                                                        GlobalPlace {
                                                            place: parent,
                                                            function: Some(global_call_site),
                                                        },
                                                        row.clone(),
                                                    )
                                                })
                                                .into_iter()
                                                .chain(std::iter::once((
                                                    GlobalPlace {
                                                        place,
                                                        function: None,
                                                    },
                                                    row,
                                                )))
                                        })
                                        .collect(),
                                )
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
            Keep::Argument(inner_location.statement_index - 1)
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
                let mut queue = place_deps[&GlobalPlace {
                    place: p,
                    function: loc.next(),
                }]
                    .iter()
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
                            queue.extend(places_read(loc.location(), &stmt_at_loc).flat_map(|pl| {
                                place_deps[&GlobalPlace {
                                    place: pl,
                                    function: p.next(),
                                }]
                                    .iter()
                                    .cloned()
                            }))
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

impl<'a, 'tcx, 'g> Flow<'a, 'tcx, 'g> {
    #[allow(dead_code)]
    fn is_transitive(&self) -> bool {
        matches!(self.kind, FlowKind::Transitive(_))
    }

    fn as_some_non_transitive_graph(
        &self,
    ) -> Option<crate::dbg::SomeNoneTransitiveGraph<'tcx, 'a, '_>> {
        match &self.kind {
            FlowKind::Transitive(_) => None,
            FlowKind::NonTransitive(t) => Some(Either::Right(&t)),
            FlowKind::NonTransitiveShrunk { shrunk, .. } => Some(Either::Left(&shrunk)),
            FlowKind::NonTransitiveRecursive { .. } => unimplemented!(),
        }
    }

    #[allow(dead_code)]
    fn aliases(&self) -> &flowistry::mir::aliases::Aliases<'a, 'tcx> {
        match &self.kind {
            FlowKind::NonTransitive(a) => &a.analysis.aliases,
            FlowKind::Transitive(a) => &a.analysis.aliases,
            FlowKind::NonTransitiveShrunk { original_flow, .. } => &original_flow.analysis.aliases,
            FlowKind::NonTransitiveRecursive { .. } => unimplemented!(),
        }
    }

    fn compute(
        opts: &crate::AnalysisCtrl,
        tcx: TyCtxt<'tcx>,
        body_id: BodyId,
        body_with_facts: &'a crate::rust::rustc_borrowck::BodyWithBorrowckFacts<'tcx>,
        gli: GLI<'g>,
    ) -> Self {
        let body = &body_with_facts.body;
        let domain = LocationDomain::new(body);
        if opts.recursive_analysis {
            let mut eval_mode = flowistry::extensions::EvalMode::default();
            let mut function_flows = RefCell::new(HashMap::new());
            eval_mode.context_mode = flowistry::extensions::ContextMode::Recurse;
            let reduced_flow = flowistry::extensions::EVAL_MODE.set(&eval_mode, || {
                compute_call_only_flow(
                    tcx,
                    &compute_granular_global_flows(tcx, gli, body_id, &function_flows).unwrap(),
                )
            });
            Self {
                domain: LocationDomain::new(body),
                kind: FlowKind::NonTransitiveRecursive {
                    root_function: body_id,
                    function_flows: function_flows,
                    reduced_flow,
                },
            }
        } else if opts.use_transitive_graph {
            Self {
                kind: FlowKind::Transitive(infoflow::compute_flow(tcx, body_id, body_with_facts)),
                domain,
            }
        } else {
            let original_flow = infoflow::compute_flow_nontransitive(tcx, body_id, body_with_facts);
            if opts.no_shrink_flow_domains {
                Self {
                    kind: FlowKind::NonTransitive(original_flow),
                    domain,
                }
            } else {
                let mut locations = body
                    .all_locations()
                    .into_iter()
                    .filter(|l| body.stmt_at(*l).is_right())
                    .collect::<Vec<_>>();
                locations.extend(flowistry::indexed::impls::arg_locations(body).1);
                let num_real_locations = locations.len();
                let shrunk_domain = Rc::new(LocationDomain::from_raw(
                    flowistry::indexed::DefaultDomain::new(locations),
                    domain.arg_block(),
                    num_real_locations,
                ));
                let shrunk = shrink_flow_domain(&original_flow, &shrunk_domain, body, tcx);
                Self {
                    kind: FlowKind::NonTransitiveShrunk {
                        original_flow,
                        shrunk,
                    },
                    domain: shrunk_domain,
                }
            }
        }
    }

    pub fn get_row<'b>(
        &'b self,
        l: mir::Location,
    ) -> &'b IndexMatrix<mir::Place<'tcx>, mir::Location> {
        match &self.kind {
            FlowKind::NonTransitive(hm) => hm.state_at(l).matrix(),
            FlowKind::Transitive(fa) => fa.state_at(l),
            FlowKind::NonTransitiveShrunk { shrunk, .. } => shrunk.get(&l).unwrap(),
            _ => unimplemented!(),
        }
    }
}

pub fn mentioned_places_with_provenance<'tcx>(
    l: mir::Location,
    body: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> impl Iterator<Item = mir::Place<'tcx>> {
    use flowistry::mir::utils::PlaceExt;
    extract_places(l, body, false)
        .into_iter()
        .flat_map(move |place| {
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

/// The idea of this function is that you can give it Flowistry's analysis and a
/// set of locations, basically a selection of "what you care about" and this
/// function will take care of collapsing all the matrices down so that
/// connections between locations that you care about are preserved, even if
/// transitive hops via locations you **don't care about** are dropped.
///
/// Example if the original MIR had
///
/// ```plain
/// Vec::push(_1, _2)
/// _3 = &_1
/// my_read(_3)
/// ```
///
/// And you instructed this function to only preserve function calls, then the
/// reduced graph would be guaranteed to still have an edge Vec::push -> my_read
fn shrink_flow_domain<'a, 'tcx, D: flowistry::infoflow::FlowDomain<'tcx>>(
    flow: &flowistry::infoflow::FlowResults<'a, 'tcx, D>,
    domain: &Rc<LocationDomain>,
    body: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> NonTransitiveGraph<'tcx> {
    let some_result = flow.state_at(mir::Location::START);
    let old_domain = &some_result.matrix().col_domain;
    domain
        .as_vec()
        .iter()
        .filter(|l| is_real_location(body, **l))
        .map(|l| {
            let old_matrix = flow.state_at(*l);
            let mut new_matrix = IndexMatrix::new(&domain);
            old_matrix.matrix().rows().for_each(|(p, s)| {
                let mut queue = s.iter().collect::<Vec<_>>();
                let mut seen = IndexSet::new(old_domain);
                while let Some(g) = queue.pop() {
                    if seen.contains(g) {
                        continue;
                    }
                    seen.insert(g);
                    if domain.contains(g) {
                        new_matrix.insert(p, *g);
                    } else if is_real_location(body, *g) {
                        let state_for_g = flow.state_at(*g).matrix();
                        queue.extend(
                            mentioned_places_with_provenance(*g, body, tcx)
                                .flat_map(|p| state_for_g.row(p)),
                        );
                    }
                }
            });
            (*l, new_matrix)
        })
        .collect()
}

type ReturnModifications<'tcx> = HashMap<Option<mir::Place<'tcx>>, Vec<DataSource>>;
enum ArgumentResolver<'tcx, 'a> {
    Root,
    Nested {
        inner: &'a ArgumentResolver<'tcx, 'a>,
        args: &'a [Option<mir::Place<'tcx>>],
        matrix: &'a IndexMatrix<mir::Place<'tcx>, mir::Location>,
        id: &'a Ident,
        body: &'a mir::Body<'tcx>,
        loc_dom: &'a LocationDomain,
        tcx: TyCtxt<'tcx>,
        accrued_returns: ReturnModifications<'tcx>,
    },
}

impl<'tcx, 'a> ArgumentResolver<'tcx, 'a> {
    fn nested(
        inner: &'a ArgumentResolver<'tcx, 'a>,
        args: &'a [Option<mir::Place<'tcx>>],
        matrix: &'a IndexMatrix<mir::Place<'tcx>, mir::Location>,
        id: &'a Ident,
        body: &'a mir::Body<'tcx>,
        loc_dom: &'a LocationDomain,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        Self::Nested {
            inner,
            args,
            matrix,
            id,
            body,
            loc_dom,
            tcx,
            accrued_returns: HashMap::new(),
        }
    }
    fn into_returns(self) -> ReturnModifications<'tcx> {
        match self {
            ArgumentResolver::Nested {
                accrued_returns, ..
            } => accrued_returns,
            _ => HashMap::new(),
        }
    }
    fn get_arg_place(&self, i: usize) -> Option<Option<mir::Place<'tcx>>> {
        match self {
            ArgumentResolver::Nested { args, .. } => Some(
                args.get(i)
                    .unwrap_or_else(|| panic!("Index {i} not found in {args:?}"))
                    .clone(),
            ),
            _ => None,
        }
    }
    fn resolve(&'a self, i: usize) -> impl Iterator<Item = DataSource> + 'a {
        match self {
            ArgumentResolver::Root => Box::new(std::iter::once(DataSource::Argument(i)))
                as Box<dyn Iterator<Item = DataSource>>,
            ArgumentResolver::Nested {
                matrix,
                inner,
                id,
                body,
                loc_dom,
                tcx,
                ..
            } => Box::new(
                self.get_arg_place(i - 1 /* There's an off-by-one here because place _0 is always the return place */)
                    .and_then(|a| a)
                    .into_iter()
                    .flat_map(|p| {
                        matrix
                            .row(p)
                            .filter_map(|l| {
                                DataSource::try_from_body(id.name, body, *l, loc_dom, *tcx, inner)
                                    .ok()
                            })
                            .flat_map(|v| v.into_iter())
                    }),
            ) as Box<_>,
        }
    }
    fn register_return(
        &mut self,
        from: DataSource,
        to: Option<mir::Place<'tcx>>,
        flows: &mut Ctrl,
    ) {
        match self {
            ArgumentResolver::Root => flows.add(Cow::Owned(from), DataSink::Return),
            ArgumentResolver::Nested {
                accrued_returns, ..
            } => accrued_returns
                .entry(to)
                .or_insert_with(Vec::new)
                .push(from),
        }
    }
}

impl DataSource {
    fn try_from_body<'tcx>(
        ident: Symbol,
        body: &mir::Body<'tcx>,
        l: mir::Location,
        domain: &LocationDomain,
        tcx: TyCtxt<'tcx>,
        mk_arg: &ArgumentResolver<'tcx, '_>,
    ) -> Result<Vec<Self>, &'static str> {
        let r = if let Some(arg) = domain.location_to_local(l) {
            let v: Vec<_> = mk_arg.resolve(arg.as_usize()).collect();
            debug!(
                "Determined the source is an argument, found {} dependencies",
                v.len()
            );
            v
        } else {
            vec![DataSource::FunctionCall(CallSite {
                called_from: Identifier::new(ident),
                function: identifier_for_fn(
                    tcx,
                    body.stmt_at(l)
                        .right()
                        .ok_or("Not a terminator")?
                        .as_fn_and_args()?
                        .0,
                ),
                location: l,
            })]
        };
        Ok(r)
    }
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

    fn handle_function<'g>(
        &self,
        hash_verifications: &mut HashVerifications,
        call_site_annotations: &mut CallSiteAnnotations,
        interesting_fn_defs: &HashMap<DefId, (Vec<Annotation>, usize)>,
        flows: &mut Ctrl,
        seen: &mut HashSet<hir::def_id::LocalDefId>,
        id: Ident,
        b: BodyId,
        local_def_id: hir::def_id::LocalDefId,
        arg_resolver: &mut ArgumentResolver<'tcx, '_>,
        gli: GLI<'g>,
    ) {
        let arg_resolver = RefCell::new(arg_resolver);
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
                &mut std::fs::OpenOptions::new()
                    .create(true)
                    .truncate(true)
                    .write(true)
                    .open(format!("{}.mir.gv", id.name))
                    .unwrap(),
            )
            .unwrap()
        }

        debug!("{}", id.name);
        let flow = Flow::compute(&self.opts.anactrl, tcx, b, body_with_facts, gli);
        let transitive_flow = infoflow::compute_flow(tcx, b, body_with_facts);

        let body = &body_with_facts.body;
        {
            let resolver_borrow = arg_resolver.borrow();
            let types = body.args_iter().flat_map(|l| {
                let ty = body.local_decls[l].ty;
                let subtypes = self.annotated_subtypes(ty);
                resolver_borrow
                    .resolve(l.as_usize())
                    .map(move |a| (a, subtypes.clone()))
            });
            flows.add_types(types);
        }
        let loc_dom = &flow.domain;
        match flow.as_some_non_transitive_graph() {
            Some(non_t_g) =>
                if self.opts.dbg.dump_non_transitive_graph {
                    crate::dbg::non_transitive_graph_as_dot(
                        &mut std::fs::OpenOptions::new()
                            .truncate(true)
                            .create(true)
                            .write(true)
                            .open(format!("{}.ntg.gv", id.name.as_str()))
                            .unwrap(),
                        body,
                        &non_t_g,
                        &flow.domain,
                        tcx,
                    )
                    .unwrap();
                    info!("Non transitive graph for {} dumped", id.name.as_str());
                } else if self.opts.dbg.dump_serialized_non_transitive_graph {
                    dump_non_transitive_graph_and_body(id, body, &non_t_g, tcx);
                }
            _ if self.opts.dbg.dump_non_transitive_graph || self.opts.dbg.dump_serialized_non_transitive_graph =>
                error!("Told to dump non-transitive graph, but analysis not instructed to make non-transitive graph!"),
            _ => ()
        }
        let mut returns_from_recursed = HashMap::new();
        for (bb, t) in body
            .basic_blocks()
            .iter_enumerated()
            .map(|(bb, bbdat)| (bb, bbdat.terminator()))
        {
            let loc = body.terminator_loc(bb);
            let matrix = flow.get_row(loc);

            if self.opts.dbg.dump_flowistry_matrix {
                info!("Flowistry matrix for {:?}", loc);
                crate::dbg::print_flowistry_matrix(&mut std::io::stdout(), matrix).unwrap();
            }

            let abstraction_info = if let Some((p, args, dest)) = t.as_fn_and_args().ok() {
                let anns = interesting_fn_defs.get(&p).map(|a| a.0.as_slice());
                debug!(
                    "{:?} {} annotations",
                    t.kind,
                    if anns.is_none() {
                        "doesn't have"
                    } else {
                        "has"
                    }
                );
                let stmt_anns = self.statement_anns_by_loc(p, t);
                let bound_sig = tcx.fn_sig(p);
                let interesting_output_types: HashSet<_> =
                    self.annotated_subtypes(bound_sig.skip_binder().output());

                let mentioned_places = args.iter().filter_map(|a| *a).collect::<HashSet<_>>();

                let src_desc = DataSource::FunctionCall(CallSite {
                    function: identifier_for_fn(tcx, p),
                    called_from: Identifier::new(id.name),
                    location: loc,
                });
                if !interesting_output_types.is_empty() {
                    flows.types.0.insert(src_desc, interesting_output_types);
                }

                if let Some(anns) = stmt_anns {
                    for ann in anns.iter().filter_map(Annotation::as_exception_annotation) {
                        hash_verifications.handle(ann, tcx, t, body, loc, matrix);
                    }
                    // TODO this is attaching to functions instead of call
                    // sites. Once we start actually tracking call sites
                    // this needs to be adjusted
                    register_call_site(tcx, call_site_annotations, p, Some(anns));
                }

                if let Some((callee_ident, callee_def_id, callee_body_id)) =
                    tcx.hir().get_if_local(p).and_then(|node| {
                        let nodeinfo = node_as_fn(&node).unwrap_or_else(|| {
                            panic!("Expected local function node, got {node:?}")
                        });
                        if seen.contains(nodeinfo.1) || anns.is_some() {
                            None
                        } else {
                            seen.insert(*nodeinfo.1);
                            Some(nodeinfo)
                        }
                    })
                {
                    debug!("Recursing into callee");
                    let resolver_borrow = arg_resolver.borrow();
                    let mut subresolver = ArgumentResolver::nested(
                        *resolver_borrow,
                        &args,
                        &matrix,
                        &id,
                        &body,
                        &loc_dom,
                        tcx,
                    );
                    self.handle_function(
                        hash_verifications,
                        call_site_annotations,
                        interesting_fn_defs,
                        flows,
                        seen,
                        *callee_ident,
                        *callee_body_id,
                        *callee_def_id,
                        &mut subresolver,
                        gli,
                    );
                    let returns = subresolver.into_returns();
                    debug!("return modification map {returns:?}");
                    returns
                        .into_iter()
                        .for_each(|(p, mods)| {
                            let the_place = p.unwrap_or(dest.unwrap().0);
                            for reachable in flow.aliases().reachable_values(the_place, mir::Mutability::Mut).iter().chain(std::iter::once(&the_place)) {
                                if let Some(old) = returns_from_recursed.insert((*reachable, loc), mods.clone()) {
                                    warn!("Duplicate function mutability override for {the_place:?} \n\twith new value \t{mods:?} \n\tand prior value\t{old:?}");
                                }
                            }
                        });
                    None
                } else {
                    debug!("Abstracting callee");
                    register_call_site(tcx, call_site_annotations, p, anns);
                    Some(
                        mentioned_places
                            .into_iter()
                            .map(|r| {
                                (
                                    r,
                                    Box::new(matrix.row(r).into_iter().cloned())
                                        as Box<dyn Iterator<Item = mir::Location>>,
                                    Either::Right(DataSink::Argument {
                                        function: CallSite {
                                            function: identifier_for_fn(tcx, p),
                                            called_from: Identifier::new(id.name),
                                            location: loc,
                                        },
                                        arg_slot: args
                                            .iter()
                                            .enumerate()
                                            .find(|(_, e)| **e == Some(r))
                                            .unwrap()
                                            .0,
                                    }),
                                )
                            })
                            .collect::<Vec<_>>(),
                    )
                }
            } else if matches!(t.kind, mir::TerminatorKind::Return) {
                match &flow.kind {
                    FlowKind::NonTransitiveShrunk { original_flow, shrunk } =>
                        debug!("Handling return for {}\n\nPre shrink matrix\n{}\n\nPost shrink matrix\n{}\n\nTransitive matrix\n{}\n", id.name, dbg::PrintableMatrix(original_flow.state_at(loc).matrix()), dbg::PrintableMatrix(&shrunk[&loc]), dbg::PrintableMatrix(transitive_flow.state_at(loc))),
                    _ => (),
                };

                Some(
                    std::iter::once((mir::Place::return_place(), Box::new(matrix.row(mir::Place::return_place()).into_iter().cloned()) as Box<_>, Either::Left(None)))
                        .chain(
                            body.args_iter()
                                .enumerate()
                                .filter(|(_, a)| body.local_decls[*a].ty.is_mutable_ptr())
                                .filter_map(|(i, local)| {
                                    let lplace = local.into();
                                    let arg_place = 
                                    arg_resolver
                                        .borrow()
                                        .get_arg_place(i);
                                    let reachable = flow.aliases().reachable_values(lplace, mir::Mutability::Not);
                                    debug!("Found mutable argument {:?} at index {i} with arg place {:?} and aliases {:?}", local, arg_resolver.borrow().get_arg_place(i), reachable);
                                    arg_place
                                        .and_then(|a| a)
                                        .map(|a| {
                                            let p = local.into();
                                            (lplace,
                                            Box::new(std::iter::once(p).chain(reachable.into_iter().cloned()).flat_map(|p| matrix.row(p)).cloned()) as Box<_>,
                                            Either::Left(Some(a)))
                                        }
                                        )
                                }),
                        )
                        .collect(),
                )
            } else {
                None
            };
            if let Some(mentioned_places) = abstraction_info {
                let mut i = 0;
                for (r, deps, sink) in mentioned_places {
                    //let deps = matrix.row(r);
                    for from in deps
                        .filter_map(|l| {
                            let from_recursed = {
                                let mut all_results = flow.aliases().aliases(r).into_iter().chain(std::iter::once(&r))
                                .filter_map(|p| returns_from_recursed.get(&(*p, l))).collect::<Vec<_>>();
                                all_results.iter().reduce(|v1, v2| {
                                    assert!(v1 == v2);
                                    v2
                                });
                                all_results.pop()
                            };

                            // Check that if we expect this function to have been recursed into that that actually happened
                            if is_real_location(body, l) {
                                body.stmt_at(l).right().map(|t| {
                                    t.as_fn_and_args().ok().map(|fninfo| {
                                        let is_local_function = tcx.hir().get_if_local(fninfo.0).and_then(|n| node_as_fn(&n)).is_some();
                                        let has_annotations = !interesting_fn_defs.get(&fninfo.0).map_or(true, |anns| anns.0.is_empty());

                                        if !(from_recursed.is_some() || !is_local_function || has_annotations) { 
                                            error!("Expected a handled subfunction '{:?}' in '{}' (place:{r:?}), but was not handled yet. Info:\n\thas_recursed:{}\n\tis_local:{is_local_function}\n\thas_annotations:{has_annotations}\n\tsearched_place:{:?}\n\taliases:{:?}\n\treachable_places:{:?}\n\treturns_map{:?}", t.kind, id.name, from_recursed.is_some(), r, flow.aliases().aliases(r), flow.aliases().reachable_values(r, mir::Mutability::Not), returns_from_recursed);
                                        }
                                    })
                                });
                            }

                            from_recursed.map(Cow::Borrowed).or(
                                DataSource::try_from_body(
                                    id.name,
                                    body,
                                    l,
                                    loc_dom,
                                    tcx,
                                    &arg_resolver.borrow(),
                                )
                                .ok()
                                .map(Cow::Owned),
                            )
                        })
                        .flat_map(|v| v.into_owned().into_iter())
                    {
                        i += 1;
                        match sink.clone() {
                            Either::Right(sink) => flows.add(Cow::Owned(from), sink),
                            Either::Left(to) => {
                                arg_resolver.borrow_mut().register_return(from, to, flows)
                            }
                        }
                    }
                }
                debug!("Found {i} flows into target.");
            }
        }
    }

    /// Handles a single target function
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
        let mut seen = HashSet::new();
        self.handle_function(
            hash_verifications,
            call_site_annotations,
            interesting_fn_defs,
            &mut flows,
            &mut seen,
            id,
            b,
            local_def_id,
            &mut ArgumentResolver::Root,
            gli,
        );
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
