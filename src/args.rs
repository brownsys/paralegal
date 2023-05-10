//! Command line arguments and parsing.
//!
//! This module deliberately hides all of the struct fields we have here. The
//! reason is that the fields and their types are used by [`clap`] as the names
//! of the command line arguments. But we might want to change the names or
//! their interpretation (e.g. go from a default positive argument like
//! `--strict` to a default negative one e.g. `--relax`). That is why instead we
//! expose methods, which do not correspond directly to those arguments but
//! allow us to change the name and default value of the argument without having
//! to migrate the code using that argument.

use std::{borrow::Cow, str::FromStr};

/// Top level command line arguments
#[derive(serde::Serialize, serde::Deserialize, clap::Args)]
pub struct Args {
    /// Print additional logging output (up to the "info" level)
    #[clap(short, long, env = "DFPP_VERBOSE")]
    verbose: bool,
    /// Print additional logging output (up to the "debug" level).
    ///
    /// Passing this flag (or env variable) with no value will enable debug
    /// output globally. You may instead pass the name of a specific target
    /// function and then only during analysis of that function the debug output
    /// is enabled.
    #[clap(long, env = "DFPP_DEBUG")]
    debug: bool,
    #[clap(long, env = "DFPP_DEBUG_TARGET")]
    debug_target: Option<String>,
    /// Where to write the resulting forge code to (defaults to `analysis_result.frg`)
    #[clap(long, default_value = "analysis_result.frg")]
    result_path: std::path::PathBuf,
    /// Emit warnings instead of aborting the analysis on sanity checks
    #[clap(long, env = "DFPP_RELAXED")]
    relaxed: bool,

    #[clap(long, env = "DFPP_TARGET")]
    target: Option<String>,
    /// Abort the compilation after finishing the analysis
    #[clap(long, env)]
    abort_after_analysis: bool,
    /// Additional arguments that control the flow analysis specifically
    #[clap(flatten, next_help_heading = "Flow Analysis")]
    anactrl: AnalysisCtrl,
    /// Additional arguments that control the generation and composition of the model
    #[clap(flatten, next_help_heading = "Model Generation")]
    modelctrl: ModelCtrl,
    /// Additional arguments that control debug args specifically
    #[clap(flatten, next_help_heading = "Debugging and Testing")]
    dbg: DbgArgs,
}

/// How a specific logging level was configured. (currently only used for the
/// `--debug` level)
#[derive(Debug, serde::Serialize, serde::Deserialize, Clone)]
pub enum LogLevelConfig<'a> {
    /// Logging for this level is only enabled for a specific target function
    Targeted(Cow<'a, str>),
    /// Logging for this level is not directly enabled
    Disabled,
    /// Logging for this level was directly enabled
    Enabled,
}

impl std::fmt::Display for LogLevelConfig<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl<'a> LogLevelConfig<'a> {
    pub fn is_enabled(&self) -> bool {
        matches!(self, LogLevelConfig::Targeted(..) | LogLevelConfig::Enabled)
    }
}

impl Args {
    pub fn target(&self) -> Option<&str> {
        self.target.as_ref().map(|s| s.as_str())
    }
    /// Returns the configuration specified for the `--debug` option
    pub fn debug(&self) -> Cow<'_, LogLevelConfig<'_>> {
        Cow::Owned(match &self.debug_target {
            Some(target) if !target.is_empty() => {
                LogLevelConfig::Targeted(Cow::Borrowed(target.as_str()))
            }
            _ if self.debug => LogLevelConfig::Enabled,
            _ => LogLevelConfig::Disabled,
        })
    }
    /// Access the debug arguments
    pub fn dbg(&self) -> &DbgArgs {
        &self.dbg
    }
    /// Access the argument controlling the analysis
    pub fn anactrl(&self) -> &AnalysisCtrl {
        &self.anactrl
    }
    pub fn modelctrl(&self) -> &ModelCtrl {
        &self.modelctrl
    }
    /// the file to write results to
    pub fn result_path(&self) -> &std::path::Path {
        self.result_path.as_path()
    }
    /// Should we output additional log messages (level `info`)
    pub fn verbose(&self) -> bool {
        self.verbose
    }
    /// Warn instead of crashing the program in case of non-fatal errors
    pub fn relaxed(&self) -> bool {
        self.relaxed
    }
    pub fn abort_after_analysis(&self) -> bool {
        self.abort_after_analysis
    }
}

#[derive(serde::Serialize, serde::Deserialize, clap::Args)]
pub struct ModelCtrl {
    /// A JSON file from which to load additional annotations. Whereas normally
    /// annotation can only be placed on crate-local items, these can also be
    /// placed on third party items, such as functions from the stdlib.
    ///
    /// The file is expected to contain a `HashMap<Identifier, (Vec<Annotation>,
    /// ObjectType)>`, which is the same type as `annotations` field from the
    /// `ProgramDescription` struct. It uses the `serde` derived serializer. An
    /// example for the format can be generated by running dfpp with
    /// `dump_serialized_flow_graph`.
    #[clap(long, env)]
    external_annotations: Option<std::path::PathBuf>,
}

impl ModelCtrl {
    /// What (if any) is the path to the file containing external annotations
    pub fn external_annotations(&self) -> Option<&std::path::Path> {
        self.external_annotations.as_ref().map(|p| p.as_path())
    }
}

/// Arguments that control the flow analysis
#[derive(serde::Serialize, serde::Deserialize, clap::Args)]
pub struct AnalysisCtrl {
    /// Disables all recursive analysis (both dfpp's inlining as well as
    /// Flowistry's recursive analysis).
    ///
    /// Also implies --no-pruning, because pruning only makes sense after inlining
    #[clap(long, env)]
    no_cross_function_analysis: bool,
    /// Do not prune paths based on unreachability via projection algebra.
    /// Essentially turns off cross-procedure field sensitivity.
    #[clap(long, env)]
    no_pruning: bool,
    #[clap(long, env)]
    pruning_strategy: Option<PruningStrategy>,
    /// Perform an aggressive removal of call sites.
    ///
    /// "conservative": removes call sites that have inputs, outputs, no
    /// control flow influence and no markers
    /// "aggressive": removes call sites that have inputs, outputs (outputs
    /// could be control flow) and no markers
    ///
    /// By default disabled entirely and no removal is performed
    #[clap(long, env)]
    remove_inconsequential_calls: Option<String>,

    #[clap(long, env)]
    drop_poll: bool,

    #[clap(long, env)]
    remove_poll_ctrl_influence: bool,
}

/// How are we treating inconsequential call sites?
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum InconsequentialCallRemovalPolicy {
    /// Remove call sites that have no markers, no control flow influence, but
    /// inputs and outputs
    Conservative,
    /// Remove call sites that have no markers, but inputs and outputs (outputs
    /// could be control flow)
    Aggressive,
    /// Remove no call sites
    Disabled,
}

impl InconsequentialCallRemovalPolicy {
    /// Are we removing call sites?
    pub fn is_enabled(self) -> bool {
        !matches!(self, InconsequentialCallRemovalPolicy::Disabled)
    }
    /// Are we removing sources of control flow?
    pub fn remove_ctrl_flow_source(self) -> bool {
        matches!(self, InconsequentialCallRemovalPolicy::Aggressive)
    }
}

#[derive(Clone, Copy, Eq, PartialEq, serde::Serialize, serde::Deserialize, Debug)]
pub enum PruningStrategy {
    NewEdgesNotPreviouslyPruned,
    NotPreviouslyPrunedEdges,
    NewEdges,
    NoPruning,
}

impl FromStr for PruningStrategy {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "minimal" => Ok(PruningStrategy::NewEdgesNotPreviouslyPruned),
            "new-edges" => Ok(PruningStrategy::NewEdges),
            "not-previously-pruned" => Ok(PruningStrategy::NotPreviouslyPrunedEdges),
            "disabled" => Ok(PruningStrategy::NoPruning),
            _ => Err(format!("Unknown pruning strategy '{s}'")),
        }
    }
}

impl PruningStrategy {
    pub fn enabled(self) -> bool {
        !matches!(self, PruningStrategy::NoPruning)
    }
}

impl AnalysisCtrl {
    /// Are we recursing into (unmarked) called functions with the analysis?
    pub fn use_recursive_analysis(&self) -> bool {
        !self.no_cross_function_analysis
    }
    /// Are we pruning with the projection algebra? (e.g. is cross function
    /// field-sensitivity enabled?)
    pub fn use_pruning(&self) -> bool {
        self.pruning_strategy().enabled()
    }

    pub fn pruning_strategy(&self) -> PruningStrategy {
        if self.no_pruning {
            assert_eq!(self.pruning_strategy, None);
            PruningStrategy::NoPruning
        } else {
            self.pruning_strategy
                .unwrap_or(PruningStrategy::NewEdgesNotPreviouslyPruned)
        }
    }

    /// What policy wrt. call site removal are we following?
    pub fn remove_inconsequential_calls(&self) -> InconsequentialCallRemovalPolicy {
        use InconsequentialCallRemovalPolicy::*;
        if let Some(s) = self.remove_inconsequential_calls.as_ref() {
            match s.as_str() {
                "conservative" => Conservative,
                "aggressive" => Aggressive,
                _ => {
                    error!("Could not parse inconsequential call removal policy '{s}', defaulting to 'conservative'.");
                    Conservative
                }
            }
        } else {
            Disabled
        }
    }

    pub fn drop_poll(&self) -> bool {
        self.drop_poll
    }
}

/// Arguments that control the output of debug information or output to be
/// consumed for testing.
#[derive(serde::Serialize, serde::Deserialize, clap::Args)]
pub struct DbgArgs {
    /// Dumps a table representing retrieved Flowistry matrices to stdout.
    #[clap(long, env)]
    dump_flowistry_matrix: bool,
    /// Dumps a dot graph representation of the finely granular, inlined flow of each controller.
    /// Unlike `dump_call_only_flow` this contains also statements and non-call
    /// terminators. It is also created differently (using dependency
    /// resolution) and has not been tested in a while and shouldn't be relied upon.
    #[clap(long, env)]
    dump_inlined_function_flow: bool,
    /// Dumps a dot graph representation of the dataflow between function calls
    /// calculated for each controller to <name of controller>.call-only-flow.gv
    #[clap(long, env)]
    dump_call_only_flow: bool,
    /// Deprecated alias for `dump_call_only_flow`
    #[clap(long, env)]
    dump_non_transitive_graph: bool,
    /// For each controller dumps the calculated dataflow graphs as well as
    /// information about the MIR to <name of controller>.ntgb.json. Can be
    /// deserialized with `crate::dbg::read_non_transitive_graph_and_body`.
    #[clap(long, env)]
    dump_serialized_non_transitive_graph: bool,
    /// Dump a complete `crate::desc::ProgramDescription` in serialized (json)
    /// format to "flow-graph.json". Used for testing.
    #[clap(long, env)]
    dump_serialized_flow_graph: bool,
    /// For each controller dump a dot representation for each [`mir::Body`] as
    /// provided by rustc
    #[clap(long, env)]
    dump_ctrl_mir: bool,
    /// Dump a `.df` file for each called function describing the dataflow
    /// matrices calculated by the flowistry-style dataflow analysis
    #[clap(long, env)]
    dump_dataflow_analysis_result: bool,
    /// Dump a `.inlined-pruned.gv` PDG for each called function describing the flow graph
    /// after pruning with the place algebra (only useful without `--no-pruning`)
    #[clap(long, env)]
    dump_inlined_pruned_graph: bool,
    /// Dump a `.inlined.gv` PDG after inlining called functions, but before pruning
    #[clap(long, env)]
    dump_inlined_graph: bool,
    /// Dump the MIR (`.mir`) of each called function (irrespective of whether they are a
    /// controller)
    #[clap(long, env)]
    dump_callee_mir: bool,
    /// Dump the flow PDG before inlining the called functions
    #[clap(long, env)]
    dump_pre_inline_graph: bool,
    /// Dump a representation of the "regal" IR for each function (`.regal`)
    #[clap(long, env)]
    dump_regal_ir: bool,
    /// Dump the equations before inlining (`.local.eqs`)
    #[clap(long, env)]
    dump_local_equations: bool,
    /// Dump the equations after inlining (`.global.eqs`)
    #[clap(long, env)]
    dump_global_equations: bool,
}

impl DbgArgs {
    pub fn dump_ctrl_mir(&self) -> bool {
        self.dump_ctrl_mir
    }
    pub fn dump_serialized_non_transitive_graph(&self) -> bool {
        self.dump_serialized_non_transitive_graph
    }
    pub fn dump_call_only_flow(&self) -> bool {
        self.dump_call_only_flow || self.dump_non_transitive_graph
    }
    pub fn dump_serialized_flow_graph(&self) -> bool {
        self.dump_serialized_flow_graph
    }
    pub fn dump_dataflow_analysis_result(&self) -> bool {
        self.dump_dataflow_analysis_result
    }
    pub fn dump_inlined_pruned_graph(&self) -> bool {
        self.dump_inlined_pruned_graph
    }
    pub fn dump_inlined_graph(&self) -> bool {
        self.dump_inlined_graph
    }
    pub fn dump_callee_mir(&self) -> bool {
        self.dump_callee_mir
    }
    pub fn dump_pre_inline_graph(&self) -> bool {
        self.dump_pre_inline_graph
    }
    pub fn dump_regal_ir(&self) -> bool {
        self.dump_regal_ir
    }
    pub fn dump_local_equations(&self) -> bool {
        self.dump_local_equations
    }
    pub fn dump_global_equations(&self) -> bool {
        self.dump_global_equations
    }
}
