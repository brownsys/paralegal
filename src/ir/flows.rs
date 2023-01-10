use super::*;
use crate::{rust::*, HashMap, HashSet};
use std::{cell::RefCell, rc::Rc};

use hir::BodyId;

use flowistry::{
    infoflow::{FlowAnalysis, NonTransitiveFlowDomain},
    mir::engine::AnalysisResults,
};
use serde::{Serialize, Deserialize};

/// The result of the data flow analysis for a function.
///
/// This gets constructed using [`Flow::compute`](Flow::compute) in
/// [`CollectingVisitor::handle_target`](crate::ana::CollectingVisitor::handle_target)
/// and is then queried to build a [`Ctrl`](crate::desc::Ctrl).
pub struct Flow<'tcx, 'g> {
    /// The id of the body for which this analysis was requested. The finely
    /// granular (includes statements and non-call terminators), inlined
    /// dataflow analysis for this body can actually be retrieved using
    /// `self.function_flows[self.root_function].unwrap()`
    pub root_function: BodyId,
    #[allow(dead_code)]
    /// Memoization of inlined, finely granular (includes statements and
    /// non-call terminators) dataflow analysis result graphs for each function
    /// called directly or indirectly from `self.root_function`.
    pub function_flows: FunctionFlows<'tcx, 'g>,
    /// The result of removing statements and terminators from the inlined graph
    /// of `self.root_function`. Also uses a representation (input dependencies
    /// vector) that abstracts away the concrete `Place`s the call is performed
    /// with.
    pub reduced_flow: CallOnlyFlow<GlobalLocation<'g>>,
}

/// A flowistry-like 3-dimensional tensor describing the [`Place`](mir::Place)
/// dependencies of all locations (including of inlined callees).
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
/// site. This is what allow us to use a plain [`Place`](mir::Place), because we
/// can perform translation at these special locations (see also
/// [`TranslatedDepMatrix`]).
///
/// The special matrix `return_state` is the union of all dependency matrices at
/// each call to `return`.
pub struct GlobalFlowGraph<'tcx, 'g> {
    pub location_states: HashMap<GlobalLocation<'g>, TranslatedDepMatrix<'tcx, 'g>>,
    pub return_state: GlobalDepMatrix<'tcx, 'g>,
}

impl<'tcx, 'g> GlobalFlowGraph<'tcx, 'g> {
    pub fn new() -> Self {
        GlobalFlowGraph {
            location_states: HashMap::new(),
            return_state: GlobalDepMatrix::new(),
        }
    }
}

/// The analysis result for one function. See [`GlobalFlowGraph`] for
/// explanations, this struct just also bundles in the [`AnalysisResults`] we
/// got from flowistry for the `self.flow.root_function`. Currently the sole
/// purpose of doing this is so that we can later query
/// `self.analysis.analysis.aliases()` to resolve `reachable_values` and
/// [`Place`](mir::Place)
/// [`aliases()`](flowistry::mir::aliases::Aliases::aliases).
pub struct FunctionFlow<'tcx, 'g> {
    pub flow: GlobalFlowGraph<'tcx, 'g>,
    pub analysis: AnalysisResults<'tcx, FlowAnalysis<'tcx, 'tcx, NonTransitiveFlowDomain<'tcx>>>,
}
/// A memoization structure used to memoize and coordinate the recursion in
/// [`GlobalFlowConstructor::compute_granular_global_flows`](crate::ana::GlobalFlowConstructor::compute_granular_global_flows).
pub type FunctionFlows<'tcx, 'g> = RefCell<HashMap<BodyId, Option<Rc<FunctionFlow<'tcx, 'g>>>>>;
/// Coarse grained, [`Place`](mir::Place) abstracted version of a
/// [`GlobalFlowGraph`].
#[derive(Serialize, Deserialize)]
#[serde(bound(
    serialize   = "Location: std::cmp::Eq + std::hash::Hash + serde::Serialize",
    deserialize = "Location: std::cmp::Eq + std::hash::Hash + serde::Deserialize<'de>"))]
pub struct CallOnlyFlow<Location> { 
    #[serde(with="crate::serializers::serde_map_via_vec")]
    pub location_dependencies: HashMap<Location, CallDeps<Location>>,
    pub return_dependencies: HashSet<Location>,
}

/// Dependencies of a function call with the [`Place`](mir::Place)s abstracted
/// away. Instead each location in the `input_deps` vector corresponds to the
/// dependencies for the positional argument at that index. For methods the 0th
/// index is `self`.
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
