//! Checking always-happens-before relationships

use std::{collections::HashSet, sync::Arc};

pub use paralegal_spdg::rustc_portable::{DefId, LocalDefId};

use paralegal_spdg::{GlobalNode, Identifier, Node, SPDGImpl};

use anyhow::{ensure, Result};
use itertools::Itertools;

use petgraph::visit::{Control, DfsEvent, GraphBase, NodeIndexable};

use crate::Diagnostics;
use crate::{
    assert_warning,
    diagnostics::{CombinatorContext, HasDiagnosticsBase},
};

/// Statistics about the result of running [`Context::always_happens_before`]
/// that are useful to understand how the property failed.
///
/// The [`std::fmt::Display`] implementation presents the information in human
/// readable form.
///
/// Note: Both the number of seen paths and the number of violation paths are
/// approximations. This is because the traversal terminates when it reaches a
/// node that was already seen. However it is guaranteed that if there
/// are any violating paths, then the number of reaching paths reported in this
/// struct is at least one (e.g. [`Self::holds`] is sound).
///
/// The stable API of this struct is [`Self::holds`], [`Self::assert_holds`] and
/// [`Self::is_vacuous`]. Otherwise the information in this struct and its
/// printed representations should be considered unstable and
/// for-human-eyes-only.
#[must_use = "call `report` or similar evaluations function to ensure the property is checked"]
pub struct AlwaysHappensBefore {
    /// How many paths terminated at the end?
    reached: Trace,
    /// How many paths lead to the checkpoints?
    checkpointed: Vec<GlobalNode>,
    /// How large was the set of initial nodes this traversal started with.
    started_with: usize,
}

impl std::fmt::Display for AlwaysHappensBefore {
    /// Format the results of this combinator, using the `def_info` to print
    /// readable names instead of ids
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} paths reached the terminal, \
            {} paths reached the checkpoints, \
            started with {} nodes",
            self.reached.len(),
            self.checkpointed.len(),
            self.started_with,
        )
    }
}

lazy_static::lazy_static! {
    static ref ALWAYS_HAPPENS_BEFORE_NAME: Identifier = Identifier::new_intern("always_happens_before");
}

impl AlwaysHappensBefore {
    /// Check this property holds and report it as diagnostics in the context.
    ///
    /// Additionally reports if the property was vacuous or had no starting
    /// nodes.
    pub fn report(&self, ctx: Arc<dyn HasDiagnosticsBase>) {
        let ctx = CombinatorContext::new(*ALWAYS_HAPPENS_BEFORE_NAME, ctx);
        assert_warning!(ctx, self.started_with != 0, "Started with 0 nodes.");
        assert_warning!(ctx, !self.is_vacuous(), "Is vacuously true.");
        if !self.holds() {
            self.reached.emit(ctx)
        }
    }

    /// Returns `true` if the property that created these statistics holds.
    pub fn holds(&self) -> bool {
        self.reached.is_empty()
    }

    /// Fails if [`Self::holds`] is false.
    pub fn assert_holds(&self) -> Result<()> {
        ensure!(
            self.holds(),
            "AlwaysHappensBefore failed: found {} violating paths",
            self.reached.len()
        );
        Ok(())
    }

    /// `true` if this policy applied to no paths. E.g. either no starting nodes
    /// or no path from them can reach the terminal or the checkpoints (the
    /// graphs are disjoined).
    pub fn is_vacuous(&self) -> bool {
        self.checkpointed.is_empty() && self.reached.is_empty()
    }
}

impl crate::Context {
    /// Enforce that on every data flow path from the `starting_points` to `is_terminal` a
    /// node satisfying `is_checkpoint` is passed.
    ///
    /// Fails if `ctrl_id` on a provided starting point is not found.
    ///
    /// The return value contains some statistics information about the
    /// traversal. The property holds if [`AlwaysHappensBefore::holds`] is true.
    ///
    /// Note that `is_checkpoint` and `is_terminal` will be called many times
    /// and should thus be efficient computations. In addition they should
    /// always return the same result for the same input.
    pub fn always_happens_before(
        &self,
        starting_points: impl IntoIterator<Item = GlobalNode>,
        mut is_checkpoint: impl FnMut(GlobalNode) -> bool,
        mut is_terminal: impl FnMut(GlobalNode) -> bool,
    ) -> Result<AlwaysHappensBefore> {
        let mut checkpointed = HashSet::new();

        let start_map = starting_points
            .into_iter()
            .map(|i| (i.controller_id(), i.local_node()))
            .into_group_map();

        let mut trace = Trace::new(self.config.always_happens_before_tracing);

        for (ctrl_id, starts) in &start_map {
            let spdg = &self.desc().controllers[&ctrl_id];
            let g = &spdg.graph;
            let mut tracer =
                Tracer::new(&mut trace, g.node_bound(), starts.iter().copied(), *ctrl_id);
            petgraph::visit::depth_first_search(g, starts.iter().copied(), |event| match event {
                DfsEvent::TreeEdge(from, to) => {
                    tracer.edge(from, to);
                    Control::<()>::Continue
                }
                DfsEvent::Discover(inner, _) => {
                    let as_node = GlobalNode::from_local_node(*ctrl_id, inner);
                    if is_checkpoint(as_node) {
                        checkpointed.insert(as_node);
                        Control::<()>::Prune
                    } else if is_terminal(as_node) {
                        tracer.terminal(inner);
                        Control::Prune
                    } else {
                        Control::Continue
                    }
                }
                _ => Control::Continue,
            });
        }

        Ok(AlwaysHappensBefore {
            reached: trace,
            checkpointed: checkpointed.into_iter().collect(),
            started_with: start_map.values().map(Vec::len).sum(),
        })
    }
}

/// Retention level of additional information about the execution of an
/// `always_happens_before`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceLevel {
    /// Keep full violating paths
    Full,
    /// Remember start and end nodes for violating paths
    StartAndEnd,
    /// Don't trace paths, only remember number of violating paths
    None,
}

struct Tracer<'a> {
    tree: Box<[Node]>,
    trace: &'a mut Trace,
    ctrl_id: LocalDefId,
}

enum Trace {
    None(usize),
    StartAndEnd(Vec<(GlobalNode, GlobalNode)>),
    Full(Vec<Vec<GlobalNode>>),
}

impl Trace {
    fn new(level: TraceLevel) -> Self {
        match level {
            TraceLevel::Full => Self::Full(vec![]),
            TraceLevel::None => Self::None(0),
            TraceLevel::StartAndEnd => Self::StartAndEnd(vec![]),
        }
    }

    fn len(&self) -> usize {
        match self {
            Self::None(s) => *s,
            Self::Full(f) => f.len(),
            Self::StartAndEnd(s) => s.len(),
        }
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn emit(&self, ctx: impl HasDiagnosticsBase) {
        match self {
            Self::None(len) => {
                let mut err = ctx.struct_error(format!("{len} nodes reached a terminal."));
                err.with_help("Enable tracing for always happens before and rerun the policy to see which terminals were reached and from where.");
                err.emit();
            }
            Self::StartAndEnd(reached) => {
                let context = ctx.as_ctx();
                for &(reached, from) in reached {
                    let from_info = context.node_info(from);
                    let reached_info = context.node_info(reached);
                    let mut err = ctx.struct_node_error(
                        reached,
                        format!(
                            "Reached this terminal {} -> {} ",
                            from_info.description, reached_info.description,
                        ),
                    );
                    err.with_node_note(from, "Started from this node");
                    err.emit();
                }
            }
            Self::Full(reached) => {
                let context = ctx.as_ctx();
                for path in reached {
                    let (reached, rest) = path
                        .split_first()
                        .expect("Invaraint broken, path must have a start");
                    let reached_info = context.node_info(*reached);
                    let mut err = ctx.struct_node_error(
                        *reached,
                        format!("Reached this terminal {}", reached_info.description,),
                    );
                    for &from in rest {
                        let from_info = context.node_info(from);
                        err.with_node_note(
                            from,
                            format!("Reached from this node {} ", from_info.description,),
                        );
                    }
                    err.emit();
                }
            }
        }
    }
}

impl<'a> Tracer<'a> {
    fn new(
        trace: &'a mut Trace,
        node_bound: usize,
        initials: impl IntoIterator<Item = Node>,
        ctrl_id: LocalDefId,
    ) -> Self {
        Self {
            tree: if matches!(trace, Trace::None(_)) {
                vec![].into()
            } else {
                let mut v: Box<[Node]> =
                    vec![<SPDGImpl as GraphBase>::NodeId::end(); node_bound].into();
                for i in initials {
                    v[i.index()] = i;
                }
                v
            },
            trace,
            ctrl_id,
        }
    }

    fn edge(&mut self, from: Node, to: Node) {
        match &self.trace {
            Trace::None(_) => (),
            Trace::StartAndEnd(..) => self.tree[to.index()] = self.tree[from.index()],
            Trace::Full(..) => self.tree[to.index()] = from,
        }
    }

    fn terminal(&mut self, mut node: Node) {
        match &mut self.trace {
            Trace::None(u) => *u += 1,
            Trace::StartAndEnd(map) => map.push((
                GlobalNode::from_local_node(self.ctrl_id, node),
                GlobalNode::from_local_node(self.ctrl_id, self.tree[node.index()]),
            )),
            Trace::Full(map) => {
                let tree = &mut self.tree;
                let ctrl_id = self.ctrl_id;
                let mut v = vec![GlobalNode::from_local_node(ctrl_id, node)];
                v.extend(std::iter::from_fn(|| {
                    let next = tree[node.index()];
                    (next != node).then(|| {
                        node = next;
                        GlobalNode::from_local_node(ctrl_id, next)
                    })
                }));
                map.push(v);
            }
        }
    }
}

#[test]
#[ignore = "Something is weird with the PDG construction here.
    See https://github.com/willcrichton/flowistry/issues/95"]
fn test_happens_before() -> Result<()> {
    use std::fs::File;
    let ctx = crate::test_utils::test_ctx();

    let start_marker = Identifier::new_intern("start");
    let bless_marker = Identifier::new_intern("bless");

    let ctrl_name = ctx.controller_by_name(Identifier::new_intern("happens_before_pass"))?;
    let ctrl = &ctx.desc().controllers[&ctrl_name];
    let f = File::create("graph.gv")?;
    ctrl.dump_dot(f)?;

    let is_terminal = |end: GlobalNode| -> bool {
        assert_eq!(end.controller_id(), ctrl_name);
        ctrl.return_.contains(&end.local_node())
    };
    let start = ctx
        .all_nodes_for_ctrl(ctrl_name)
        .filter(|n| ctx.has_marker(start_marker, *n))
        .collect::<Vec<_>>();

    let pass = ctx.always_happens_before(
        start,
        |checkpoint| ctx.has_marker(bless_marker, checkpoint),
        is_terminal,
    )?;

    ensure!(pass.holds(), "{pass}");
    ensure!(!pass.is_vacuous(), "{pass}");

    let ctrl_name = ctx.controller_by_name(Identifier::new_intern("happens_before_fail"))?;

    let fail = ctx.always_happens_before(
        ctx.all_nodes_for_ctrl(ctrl_name)
            .filter(|n| ctx.has_marker(start_marker, *n)),
        |check| ctx.has_marker(bless_marker, check),
        is_terminal,
    )?;

    ensure!(!fail.holds());
    ensure!(!fail.is_vacuous());

    Ok(())
}
