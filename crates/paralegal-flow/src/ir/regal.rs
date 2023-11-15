use flowistry::indexed::{
    impls::{build_location_arg_domain, LocationOrArg},
    IndexedDomain,
};
use mir::{AggregateKind, Rvalue};
use paralegal_spdg::rustc_portable::DefId;
use rustc_ast::ptr::P;
use rustc_utils::{mir::control_dependencies::ControlDependencies, BodyExt};

use crate::{
    ana::{
        algebra::{self, Equality, MirEquation, Term},
        df,
        inline::InlineJudge,
    },
    hir::def_id::LocalDefId,
    ir::TypedLocal,
    mir::{self, BasicBlock, HasLocalDecls, Location},
    rust::{rustc_ast, rustc_index::bit_set::HybridBitSet, rustc_index::vec::IndexVec},
    utils::{
        body_name_pls, dump_file_pls, time, write_sep, AsFnAndArgs, AsFnAndArgsErr,
        DisplayViaDebug, FnResolution, TyCtxtExt,
    },
    DumpArgs, Either, HashMap, HashSet, MarkerCtx, TyCtxt,
};

use std::fmt::{Display, Write};

newtype_index!(
    #[debug_format = "arg{}"]
    pub struct ArgumentIndex {}
);

impl From<mir::Local> for ArgumentIndex {
    fn from(value: mir::Local) -> Self {
        assert_ne!(value, mir::RETURN_PLACE);
        Self::from_usize(value.as_usize() - 1)
    }
}

impl From<ArgumentIndex> for mir::Local {
    fn from(value: ArgumentIndex) -> Self {
        Self::from_usize(value.as_usize() + 1)
    }
}

impl Display for ArgumentIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "a{}", self.as_usize())
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub enum TargetPlace {
    Return,
    Argument(ArgumentIndex),
}

#[derive(Hash, Eq, PartialEq, Debug, Copy, Clone)]
pub enum Target<L> {
    Call(L),
    Argument(ArgumentIndex),
}

impl<L: allocative::Allocative> allocative::Allocative for Target<L> {
    fn visit<'a, 'b: 'a>(&self, visitor: &'a mut allocative::Visitor<'b>) {
        const call: allocative::Key = allocative::Key::new("call");
        let mut vis = visitor.enter_self_sized::<Self>();
        if let Target::Call(c) = self {
            vis.visit_field(call, c)
        }
        vis.exit()
    }
}

impl From<LocationOrArg> for Target<DisplayViaDebug<Location>> {
    fn from(value: LocationOrArg) -> Self {
        match value {
            LocationOrArg::Arg(a) => Target::Argument(a.into()),
            LocationOrArg::Location(loc) => Target::Call(loc.into()),
        }
    }
}

impl<L> Target<L> {
    pub fn map_location<L0, F: FnMut(&L) -> L0>(&self, mut f: F) -> Target<L0> {
        match self {
            Target::Argument(a) => Target::Argument(*a),
            Target::Call(l) => Target::Call(f(l)),
        }
    }
}

impl<L: Display> Display for Target<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Target::Call(loc) => write!(f, "{loc}"),
            Target::Argument(a) => a.fmt(f),
        }
    }
}

#[derive(Debug)]
pub struct Call<'tcx, D> {
    pub function: FnResolution<'tcx>,
    pub arguments: IndexVec<ArgumentIndex, Option<(TypedLocal<'tcx>, D)>>,
    pub return_to: Option<TypedLocal<'tcx>>,
    pub ctrl_deps: D,
    pub span: crate::Span,
}

impl<'tcx, D: allocative::Allocative> allocative::Allocative for Call<'tcx, D> {
    fn visit<'a, 'b: 'a>(&self, visitor: &'a mut allocative::Visitor<'b>) {
        const function: allocative::Key = allocative::Key::new("function");
        const arguments: allocative::Key = allocative::Key::new("arguments");
        const return_to: allocative::Key = allocative::Key::new("return_to");
        const ctrl_deps: allocative::Key = allocative::Key::new("ctrl_deps");
        let mut vis = visitor.enter_self(self);
        vis.visit_field(function, &self.function);
        vis.visit_field(
            arguments,
            &crate::utils::VisitViaClosure(|v: &'_ mut allocative::Visitor<'_>| {
                self.arguments.raw.visit(v)
            }),
        );
        vis.visit_field(return_to, &self.return_to);
        vis.visit_field(ctrl_deps, &self.ctrl_deps);
        vis.visit_simple_sized::<crate::Span>();
        vis.exit()
    }
}

impl<'tcx, D> Call<'tcx, D> {
    pub fn argument_locals(&self) -> impl Iterator<Item = TypedLocal<'tcx>> + '_ {
        self.arguments
            .iter()
            .filter_map(|a| a.as_ref().map(|i| i.0))
    }
}

// struct NeverInline;

// impl RecurseSelector for NeverInline {
//     fn is_selected<'tcx>(&self, _tcx: TyCtxt<'tcx>, _tk: &mir::TerminatorKind<'tcx>) -> bool {
//         false
//     }
// }

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub struct RelativePlace<L> {
    pub location: L,
    pub place: TargetPlace,
}

impl<L: Display> Display for RelativePlace<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} @ {}", self.location, self.place)
    }
}

pub type Dependencies<L> = HashSet<Target<L>>;

fn fmt_deps<L: Display>(
    deps: &Dependencies<L>,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    f.write_char('{')?;
    let mut first_dep = true;
    for dep in deps {
        if first_dep {
            first_dep = false;
        } else {
            f.write_str(", ")?;
        }
        write!(f, "{dep}")?;
    }
    f.write_char('}')
}

impl<'tcx, L: Display> Display for Call<'tcx, Dependencies<L>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('(')?;
        write_sep(f, ", ", self.arguments.iter(), |elem, f| {
            if let Some((place, deps)) = elem {
                fmt_deps(deps, f)?;
                write!(f, " with {place:?}")
            } else {
                f.write_str("{}")
            }
        })?;
        write!(f, ") ctrl:")?;
        fmt_deps(&self.ctrl_deps, f)?;
        write!(f, " return:{:?}", self.return_to)?;
        write!(f, " {:?}", self.function)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Ord, PartialOrd)]
pub enum SimpleLocation<C> {
    Return,
    Argument(ArgumentIndex),
    Call(C),
}

impl<L> SimpleLocation<L> {
    pub fn map_location<L0, F: FnMut(&L) -> L0>(&self, mut f: F) -> SimpleLocation<L0> {
        use SimpleLocation::*;
        match self {
            Argument(a) => Argument(*a),
            Call(l) => Call(f(l)),
            Return => Return,
        }
    }
}

impl<D: std::fmt::Display, O: std::fmt::Display> std::fmt::Display for SimpleLocation<(D, O)> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use SimpleLocation::*;
        match self {
            Return => f.write_str("ret"),
            Argument(a) => write!(f, "{a:?}"),
            Call((gloc, did)) => write!(f, "{gloc} ({did})"),
        }
    }
}

impl<D: std::fmt::Display> std::fmt::Display for SimpleLocation<RelativePlace<D>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use SimpleLocation::*;
        match self {
            Return => f.write_str("ret"),
            Argument(a) => write!(f, "{a:?}"),
            Call(c) => write!(f, "{c}"),
        }
    }
}

#[cfg_attr(feature = "profiling", derive(allocative::Allocative))]
#[derive(Debug)]
pub struct Body<'tcx, L> {
    pub calls: HashMap<L, Call<'tcx, Dependencies<L>>>,
    pub return_deps: Dependencies<L>,
    pub return_arg_deps: Vec<Dependencies<L>>,
    pub equations: Vec<MirEquation<'tcx>>,
}

impl<'tcx, L: Display + Ord> Display for Body<'tcx, L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ordered = self.calls.iter().collect::<Vec<_>>();
        ordered.sort_by_key(|t| t.0);
        for (loc, call) in ordered {
            writeln!(f, "{:<6}: {}", format!("{}", loc), call)?
        }
        write!(f, "return: ")?;
        fmt_deps(&self.return_deps, f)?;
        writeln!(f)?;
        write!(f, "return args: (")?;
        let mut first_arg = true;
        for arg in &self.return_arg_deps {
            if first_arg {
                first_arg = false;
            } else {
                f.write_str(", ")?;
            }
            fmt_deps(arg, f)?;
        }
        f.write_char(')')?;
        writeln!(f)?;
        writeln!(f, "equations:")?;
        for eq in self.equations.iter() {
            writeln!(f, "  {eq}")?;
        }
        Ok(())
    }
}

pub fn get_highest_local(body: &mir::Body) -> mir::Local {
    use mir::visit::Visitor;
    struct Extractor(Option<mir::Local>);
    impl Visitor<'_> for Extractor {
        fn visit_local(
            &mut self,
            local: mir::Local,
            _context: mir::visit::PlaceContext,
            _location: Location,
        ) {
            let m = self.0.get_or_insert(local);
            if *m < local {
                *m = local;
            }
        }
    }
    let mut e = Extractor(None);
    e.visit_body(body);
    e.0.unwrap_or(mir::RETURN_PLACE)
}

impl<'tcx> Body<'tcx, DisplayViaDebug<Location>> {
    #[cfg_attr(feature = "profiling", flamer::flame)]
    pub fn construct<I: IntoIterator<Item = algebra::MirEquation<'tcx>>>(
        flow_analysis: df::FlowResults<'_, 'tcx, '_>,
        equations: I,
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        body_with_facts: &'tcx rustc_utils::mir::borrowck_facts::CachedSimplifedBodyWithFacts<'tcx>,
    ) -> Self {
        let domain = build_location_arg_domain(body_with_facts.simplified_body());
        let name = body_name_pls(tcx, def_id).name;
        time(&format!("Regal Body Construction of {name}"), || {
            let body = flow_analysis.analysis.body;
            let ctrl_ana = &flow_analysis.analysis.control_dependencies;
            let non_transitive_aliases =
                crate::ana::non_transitive_aliases::compute(tcx, def_id, body_with_facts);

            let dependencies_for =
                |location: DisplayViaDebug<_>, arg| -> Dependencies<DisplayViaDebug<_>> {
                    use rustc_ast::Mutability;
                    let ana = flow_analysis.state_at(*location);
                    let mutability = Mutability::Not;
                    // Not sure this is necessary anymore because I changed the analysis
                    // to transitively propagate in cases where a subplace is modified
                    let reachable_values = non_transitive_aliases.reachable_values(arg, mutability);
                    // debug!("Reachable values for {arg:?} are {reachable_values:?}");
                    // debug!(
                    //     "  Children are {:?}",
                    //     reachable_values
                    //         .into_iter()
                    //         .flat_map(|a| non_transitive_aliases.children(*a))
                    //         .collect::<Vec<_>>()
                    // );
                    let deps = reachable_values
                        .iter()
                        .flat_map(|p| non_transitive_aliases.children(*p))
                        // Commenting out this filter because reachable values doesn't
                        // always contain all relevant subplaces
                        //.filter(|p| !is_mut_arg || p != &arg)
                        .flat_map(|place| ana.deps(non_transitive_aliases.normalize(place)))
                        .map(|&(dep_loc, _dep_place)| (*domain.value(dep_loc)).into())
                        .collect();
                    deps
                };
            let mut call_argument_equations = HashSet::new();
            let mut next_new_local = get_highest_local(body);
            let calls = body
                .basic_blocks
                .iter_enumerated()
                .filter(|(bb, _dat)| {
                    !flow_analysis
                        .analysis
                        .elision_info()
                        .contains_key(&body.terminator_loc(*bb))
                })
                .filter_map(|(bb, bbdat)| {
                    let (function, mut simple_args, ret) =
                        match bbdat.terminator().as_instance_and_args(tcx) {
                            Ok(p) => p,
                            Err(AsFnAndArgsErr::NotAFunctionCall) => return None,
                            Err(e) => panic!("{e:?}"),
                        };
                    let bbloc = DisplayViaDebug(body.terminator_loc(bb));
                    if let Ok(fn_sig) = function.sig(tcx)
                        && fn_sig.abi == crate::rustc_target::spec::abi::Abi::RustCall {
                        // If we are dealing with a "rust-call" style call then
                        // the second argument is a tuple where each field of
                        // the tuple must be passed separately.
                        let base = simple_args.pop().unwrap().unwrap();
                        assert_eq!(simple_args.len(), 1);
                        assert!(!fn_sig.inputs().is_empty());
                        simple_args.extend(
                            fn_sig.inputs().iter().enumerate().map(|(i, _)|
                                Some(base.project_deeper(&[mir::ProjectionElem::Field(i.into(), base.ty(body, tcx).field_ty(tcx, i.into()))], tcx))
                            )
                        )
                    }

                    let arguments = IndexVec::from_raw(
                        simple_args
                            .into_iter()
                            .map(|arg| {
                                arg.map(|a| {
                                    let ty = a.ty(body, tcx);
                                    let local = if a.projection.is_empty() {
                                        TypedLocal::new_with_type(a.local, ty.ty)
                                    } else {
                                        use crate::rust::rustc_index::vec::Idx;
                                        next_new_local.increment_by(1);
                                        assert!(ty.variant_index.is_none());
                                        let typed_local = TypedLocal::new_with_type(next_new_local, ty.ty);
                                        call_argument_equations.insert(Equality::new_mir(
                                            tcx,
                                            Term::new_base(typed_local),
                                            Term::from_place(a, body),
                                            false,
                                        ));
                                        typed_local
                                    };
                                    (local, dependencies_for(bbloc, a))
                                })
                            })
                            .collect(),
                    );
                    let ctrl_deps = recursive_ctrl_deps(ctrl_ana, bb, body, dependencies_for);
                    assert!(ret.projection.is_empty());
                    let return_to = Some(TypedLocal::new(ret.local, body));
                    Some((
                        bbloc,
                        Call {
                            function,
                            arguments,
                            ctrl_deps,
                            return_to,
                            span: bbdat.terminator().source_info.span,
                        },
                    ))
                })
                .collect();
            let mut return_arg_deps: Vec<(mir::Place<'tcx>, _)> = body
                .args_iter()
                .flat_map(|a| {
                    let place = mir::Place::from(a);
                    let local_decls = body.local_decls();
                    let ty = place.ty(local_decls, tcx).ty;
                    // Arguments are only visible to the outside if they are
                    // pointers. But we wouldn't see any changes to the pointer
                    // itself, only the value it points to, hence the additional
                    // `Deref`. We don't handle `Rc` or `Arc` at the moment.
                    //
                    // It may actually be necessary to `walk` the type here to
                    // discover references on its inside.
                    if ty.is_mutable_ptr() {
                        Either::Left(
                            Some(place.project_deeper(&[mir::PlaceElem::Deref], tcx)).into_iter(),
                        )
                    } else if ty.is_generator() {
                        // Should this also apply to closures?
                        Either::Right(
                            non_transitive_aliases
                                .children(place)
                                .into_iter()
                                .filter_map(|child| {
                                    child.ty(local_decls, tcx).ty.is_mutable_ptr().then(|| {
                                        child.project_deeper(&[mir::PlaceElem::Deref], tcx)
                                    })
                                }),
                        )
                    } else {
                        Either::Left(None.into_iter())
                    }
                })
                .map(|p| (p, HashSet::new()))
                .collect();
            let return_deps = body
                .all_returns()
                .map(DisplayViaDebug)
                .flat_map(|loc| {
                    return_arg_deps.iter_mut().for_each(|(i, s)| {
                        for d in dependencies_for(loc, *i) {
                            s.insert(d);
                        }
                    });
                    dependencies_for(loc, mir::Place::return_place()).into_iter()
                })
                .collect();

            let equations = equations
                .into_iter()
                .chain(call_argument_equations)
                .collect::<Vec<_>>();

            Self {
                calls,
                return_deps,
                return_arg_deps: return_arg_deps.into_iter().map(|(_, s)| s).collect(),
                equations,
            }
        })
    }
}

/// Uhh, so this function is kinda ugly. It tries to make sure we're not missing
/// control flow edges, but at the same time it also tries to preserve
/// non-transitivity among control flow dependencies. What this means is that if
/// you have a case like
///
/// ```
/// let y = baz();
/// if y {
///   let x = foo();
///   if x {
///     bar(...);
///   }
/// }
/// ```
///
/// Then `foo` will be a control dependency of `bar`, but `baz` will not.
/// Instead that is only a transitive dependency because `baz` is a ctrl
/// dependency of `foo`.
///
/// XXX: These semantics are what I believed we wanted, but we haven't discussed
/// if this is the right thing to do.
fn recursive_ctrl_deps<
    'tcx,
    F: FnMut(DisplayViaDebug<Location>, mir::Place<'tcx>) -> Dependencies<DisplayViaDebug<Location>>,
>(
    ctrl_ana: &ControlDependencies<BasicBlock>,
    bb: mir::BasicBlock,
    body: &mir::Body<'tcx>,
    mut dependencies_for: F,
) -> Dependencies<DisplayViaDebug<Location>> {
    let mut seen = ctrl_ana
        .dependent_on(bb)
        .cloned()
        .unwrap_or_else(|| HybridBitSet::new_empty(0));
    let mut queue = seen.iter().collect::<Vec<_>>();
    let mut dependencies = Dependencies::new();
    while let Some(block) = queue.pop() {
        seen.insert(block);
        let terminator = body.basic_blocks[block].terminator();
        if let mir::TerminatorKind::SwitchInt { discr, .. } = &terminator.kind {
            if let Some(discr_place) = discr.place() {
                let deps =
                    dependencies_for(DisplayViaDebug(body.terminator_loc(block)), discr_place);
                for d in &deps {
                    if let Target::Call(loc) = d {
                        seen.insert(loc.block);
                    }
                }
                dependencies.extend(deps);

                if let Some(mut switch_deps) = ctrl_ana.dependent_on(block).cloned() {
                    switch_deps.subtract(&seen);
                    queue.extend(switch_deps.iter());
                }

                // This is where things go off the rails.
                //
                // The reason this is so complicated is because rustc desugars
                // `&&` and `||` in an annoying way. The details are explained
                // in
                // https://www.notion.so/justus-adam/Control-flow-with-non-fn-statement-does-not-create-the-ctrl_flow-relation-correctly-3993e8fd86d54f51bfa75fde447b81ec
                let predecessors = &body.basic_blocks.predecessors()[block];
                if predecessors.len() > 1 {
                    enum SetResult<A> {
                        Uninit,
                        Unequal,
                        Set(A),
                    }
                    if let SetResult::Set(parent_deps) = {
                        use mir::visit::Visitor;
                        struct AssignsCheck<'tcx> {
                            target: mir::Place<'tcx>,
                            was_assigned: bool,
                        }
                        impl<'tcx> Visitor<'tcx> for AssignsCheck<'tcx> {
                            fn visit_assign(
                                &mut self,
                                place: &mir::Place<'tcx>,
                                _rvalue: &mir::Rvalue<'tcx>,
                                _location: Location,
                            ) {
                                self.was_assigned |= *place == self.target;
                            }
                            fn visit_terminator(
                                &mut self,
                                terminator: &mir::Terminator<'tcx>,
                                _location: Location,
                            ) {
                                if let mir::TerminatorKind::Call { destination, .. } =
                                    terminator.kind
                                {
                                    self.was_assigned |= destination == self.target
                                }
                            }
                        }

                        predecessors
                            .iter()
                            .fold(SetResult::Uninit, |prev_deps, &block| {
                                if matches!(prev_deps, SetResult::Unequal) {
                                    return SetResult::Unequal;
                                }
                                let ctrl_deps =
                                    if let Some(ctrl_deps) = ctrl_ana.dependent_on(block) {
                                        ctrl_deps
                                    } else {
                                        return SetResult::Unequal;
                                    };
                                let data = &body.basic_blocks[block];
                                let mut check = AssignsCheck {
                                    target: discr_place,
                                    was_assigned: false,
                                };
                                check.visit_basic_block_data(block, data);
                                if !check.was_assigned {
                                    return SetResult::Unequal;
                                }
                                match prev_deps {
                                    SetResult::Uninit => SetResult::Set(ctrl_deps),
                                    SetResult::Set(other)
                                        if !other.superset(ctrl_deps)
                                            || !ctrl_deps.superset(other) =>
                                    {
                                        SetResult::Unequal
                                    }
                                    _ => prev_deps,
                                }
                            })
                    } {
                        queue.extend(parent_deps.iter());
                    }
                }
            }
        }
    }
    dependencies
}

fn warn_if_marked_type_constructed<'tcx>(
    tcx: TyCtxt<'tcx>,
    marker_ctx: MarkerCtx<'tcx>,
    def_id: crate::DefId,
    body: &mir::Body<'tcx>,
) {
    struct WarnVisitor<'tcx> {
        marker_ctx: MarkerCtx<'tcx>,
        tcx: TyCtxt<'tcx>,
        fun: crate::DefId,
    }

    impl<'tcx> mir::visit::Visitor<'tcx> for WarnVisitor<'tcx> {
        fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: Location) {
            if let Rvalue::Aggregate(box AggregateKind::Adt(did, ..), _) = rvalue
                && self.marker_ctx.is_marked(did)
            {
                warn!("Found constructor for marked ADT type {} in {} at {:?}. This can cause unsoundness as this value will not carry the marker.", self.tcx.def_path_debug_str(*did), self.tcx.def_path_debug_str(self.fun), location)
            }
        }
    }

    let mut vis = WarnVisitor {
        tcx,
        fun: def_id,
        marker_ctx,
    };

    mir::visit::Visitor::visit_body(&mut vis, body)
}

/// Returns `None` if we were unable to retrieve a body for the function
/// referenced by `def_id` (usually caused by the use of trait objects).
pub fn compute_from_def_id<'tcx>(
    dbg_opts: &DumpArgs,
    def_id: DefId,
    tcx: TyCtxt<'tcx>,
    carries_marker: &InlineJudge<'tcx>,
) -> Option<Body<'tcx, DisplayViaDebug<Location>>> {
    let local_def_id = def_id.expect_local();
    info!("Analyzing function {}", body_name_pls(tcx, local_def_id));
    let body_with_facts = tcx.body_for_def_id_default_policy(def_id)?;
    let body = body_with_facts.simplified_body();
    warn_if_marked_type_constructed(
        tcx,
        carries_marker.marker_ctx().clone(),
        local_def_id.to_def_id(),
        body,
    );
    let flow = df::compute_flow_internal(tcx, def_id, body_with_facts, carries_marker);
    if dbg_opts.dump_callee_mir() {
        mir::pretty::write_mir_fn(
            tcx,
            body,
            &mut |_, _| Ok(()),
            &mut dump_file_pls(tcx, local_def_id, "mir").unwrap(),
        )
        .unwrap();
    }
    if dbg_opts.dump_dataflow_analysis_result() {
        use std::io::Write;
        let states_out = &mut dump_file_pls(tcx, local_def_id, "df").unwrap();
        for l in body.all_locations() {
            writeln!(states_out, "{l:?}: {}", flow.state_at(l)).unwrap();
        }
    }
    let mut equations = algebra::extract_equations(tcx, body);
    equations.extend(
        flow.analysis
            .elision_info()
            .values()
            .flat_map(|i| i.iter())
            .cloned(),
    );
    let r = Body::construct(flow, equations, tcx, local_def_id, body_with_facts);
    if dbg_opts.dump_regal_ir() {
        let mut out = dump_file_pls(tcx, local_def_id, "regal").unwrap();
        use std::io::Write;
        write!(&mut out, "{}", r).unwrap();
    }
    Some(r)
}
