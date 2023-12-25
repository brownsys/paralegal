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

use anyhow::Error;
use clap::ValueEnum;
use std::str::FromStr;

use crate::utils::TinyBitSet;
use crate::{num_derive, num_traits::FromPrimitive};

impl TryFrom<ClapArgs> for Args {
    type Error = Error;
    fn try_from(value: ClapArgs) -> Result<Self, Self::Error> {
        let ClapArgs {
            verbose,
            debug,
            debug_target,
            result_path,
            graph_loc_path,
            relaxed,
            target,
            abort_after_analysis,
            anactrl,
            modelctrl,
            dump,
            marker_control,
        } = value;
        let mut dump: DumpArgs = dump.into();
        if let Ok(from_env) = std::env::var("PARALEGAL_DUMP") {
            let from_env =
                DumpArgs::from_str(&from_env, false).map_err(|s| anyhow::anyhow!("{}", s))?;
            dump.0 |= from_env.0;
        }
        let build_config_file = std::path::Path::new("Paralegal.toml");
        let build_config = if build_config_file.exists() {
            toml::from_str(&std::fs::read_to_string(build_config_file)?)?
        } else {
            Default::default()
        };
        let log_level_config = match debug_target {
            Some(target) if !target.is_empty() => LogLevelConfig::Targeted(target),
            _ if debug => LogLevelConfig::Enabled,
            _ => LogLevelConfig::Disabled,
        };
        Ok(Args {
            verbose,
            log_level_config,
            result_path,
            graph_loc_path,
            relaxed,
            target,
            abort_after_analysis,
            anactrl,
            modelctrl,
            dump,
            build_config,
            marker_control,
        })
    }
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct Args {
    /// Print additional logging output (up to the "info" level)
    verbose: bool,
    log_level_config: LogLevelConfig,
    /// Where to write the resulting forge code to (defaults to `analysis_result.frg`)
    result_path: std::path::PathBuf,
    /// Where to write the resulting GraphLocation (defaults to `flow-graph.json`)
    pub(crate) graph_loc_path: std::path::PathBuf,
    /// Emit warnings instead of aborting the analysis on sanity checks
    relaxed: bool,

    target: Option<String>,
    /// Abort the compilation after finishing the analysis
    abort_after_analysis: bool,
    /// Additional arguments on marker assignment and discovery
    marker_control: MarkerControl,
    /// Additional arguments that control the flow analysis specifically
    anactrl: AnalysisCtrl,
    /// Additional arguments that control the generation and composition of the model
    modelctrl: ModelCtrl,
    /// Additional arguments that control debug output specifically
    dump: DumpArgs,
    /// Additional configuration for the build process/rustc
    build_config: BuildConfig,
}

/// Arguments as exposed on the command line.
///
/// You should then use `try_into` to convert this to [`Args`], the argument
/// structure used internally.
#[derive(clap::Args)]
pub struct ClapArgs {
    /// Print additional logging output (up to the "info" level)
    #[clap(short, long, env = "PARALEGAL_VERBOSE")]
    verbose: bool,
    /// Print additional logging output (up to the "debug" level).
    ///
    /// Passing this flag (or env variable) with no value will enable debug
    /// output globally. You may instead pass the name of a specific target
    /// function and then only during analysis of that function the debug output
    /// is enabled.
    #[clap(long, env = "PARALEGAL_DEBUG")]
    debug: bool,
    #[clap(long, env = "PARALEGAL_DEBUG_TARGET")]
    debug_target: Option<String>,
    /// Where to write the resulting forge code to (defaults to `analysis_result.frg`)
    #[clap(long, default_value = "analysis_result.frg")]
    result_path: std::path::PathBuf,
    /// Where to write the resulting GraphLocation (defaults to `flow-graph.json`)
    #[clap(long, default_value = "flow-graph.json")]
    graph_loc_path: std::path::PathBuf,
    /// Emit warnings instead of aborting the analysis on sanity checks
    #[clap(long, env = "PARALEGAL_RELAXED")]
    relaxed: bool,

    #[clap(long, env = "PARALEGAL_TARGET")]
    target: Option<String>,
    /// Abort the compilation after finishing the analysis
    #[clap(long, env)]
    abort_after_analysis: bool,
    /// Additional arguments that control the flow analysis specifically
    #[clap(flatten, next_help_heading = "Flow Analysis")]
    anactrl: AnalysisCtrl,
    /// Additional arguments which control marker assignment and discovery
    #[clap(flatten, next_help_heading = "Marker Control")]
    marker_control: MarkerControl,
    /// Additional arguments that control the generation and composition of the model
    #[clap(flatten, next_help_heading = "Model Generation")]
    modelctrl: ModelCtrl,
    /// Additional arguments that control debug args specifically
    #[clap(flatten)]
    dump: ParseableDumpArgs,
}

#[derive(Clone, clap::Args)]
pub struct ParseableDumpArgs {
    /// Generate intermediate of various formats and at various stages of
    /// compilation. A short description of each value is provided here, for a
    /// more comprehensive explanation refer to the [notion page on
    /// dumping](https://www.notion.so/justus-adam/Dumping-Intermediate-Representations-4bd66ec11f8f4c459888a8d8cfb10e93).
    ///
    /// Can also be supplied as a comma-separated list (no spaces) and be set with the `PARALEGAL_DUMP` variable.
    #[clap(long, value_enum)]
    dump: Vec<DumpArgs>,
}

lazy_static! {
    static ref DUMP_ARGS_OPTIONS: Vec<DumpArgs> = DumpOption::value_variants()
        .iter()
        .map(|&v| v.into())
        .collect();
}

impl clap::ValueEnum for DumpArgs {
    fn value_variants<'a>() -> &'a [Self] {
        &DUMP_ARGS_OPTIONS
    }

    fn to_possible_value(&self) -> Option<clap::builder::PossibleValue> {
        let mut it = self.0.into_iter_set_in_domain();
        let v = it.next().unwrap();
        assert!(it.next().is_none());
        DumpOption::from_u32(v).unwrap().to_possible_value()
    }

    fn from_str(input: &str, ignore_case: bool) -> Result<Self, String> {
        input
            .split(',')
            .map(|segment| DumpOption::from_str(segment, ignore_case))
            .collect()
    }
}

impl From<DumpOption> for DumpArgs {
    fn from(value: DumpOption) -> Self {
        [value].into_iter().collect()
    }
}

impl From<ParseableDumpArgs> for DumpArgs {
    fn from(value: ParseableDumpArgs) -> Self {
        value.dump.into_iter().flat_map(|opt| opt.iter()).collect()
    }
}

/// Collection of the [`DumpOption`]s a user has set.
///
/// Separates the cli and the internal api. Users set [`DumpOption`]s in the
/// cli, internally we use the snake-case version of the option as a method on
/// this type. This is so we can rename the outer UI without breaking code or
/// even combine options together.
///
/// As of writing these docs clap doesn't have a way to attach extra constraints
/// to a derived impl (e.g. `Args` of `GArgs`). And so it has to be added to the
/// type variable at the struct definition itself. That means this compressed
/// type, that is only meant to be queried but not parsed needs an impl for
/// these contraints, hence the `undefined!()`.
#[derive(serde::Serialize, serde::Deserialize, Clone)]
pub struct DumpArgs(TinyBitSet);

impl DumpArgs {
    fn iter(self) -> impl Iterator<Item = DumpOption> {
        self.0
            .into_iter_set_in_domain()
            .filter_map(DumpOption::from_u32)
    }
}

impl FromIterator<DumpOption> for DumpArgs {
    fn from_iter<T: IntoIterator<Item = DumpOption>>(iter: T) -> Self {
        Self(iter.into_iter().map(|v| v as u32).collect())
    }
}

#[derive(
    Copy,
    Clone,
    Eq,
    PartialEq,
    serde::Serialize,
    serde::Deserialize,
    clap::ValueEnum,
    num_derive::FromPrimitive,
)]
enum DumpOption {
    /// For each controller dump a dot representation for each [`mir::Body`] as
    /// provided by rustc
    CtrlMir,
    /// For each controller dumps the calculated dataflow graphs as well as
    /// information about the MIR to <name of controller>.ntgb.json. Can be
    /// deserialized with `crate::dbg::read_non_transitive_graph_and_body`.
    SerializedNonTransitiveGraph,
    /// Dumps a dot graph representation of the dataflow between function calls
    /// calculated for each controller to <name of controller>.call-only-flow.gv
    CallOnlyFlow,
    /// Dump a complete `crate::desc::ProgramDescription` in serialized (json)
    /// format to "flow-graph.json". Used for testing.
    SerializedFlowGraph,
    /// Dump a `.df` file for each called function describing the dataflow
    /// matrices calculated by the flowistry-style dataflow analysis
    DataflowAnalysisResult,
    /// Dump a `.inlined-pruned.gv` PDG for each called function describing the flow graph
    /// after pruning with the place algebra (only useful without `--no-pruning`)
    InlinedPrunedGraph,
    /// Dump a `.inlined.gv` PDG after inlining called functions, but before pruning
    InlinedGraph,
    /// Dump the MIR (`.mir`) of each called function (irrespective of whether they are a
    /// controller)
    CalleeMir,
    /// Dump the flow PDG before inlining the called functions
    PreInlineGraph,
    /// Dump a representation of the "regal" IR for each function (`.regal`)
    RegalIr,
    /// Dump the equations before inlining (`.local.eqs`)
    LocalEquations,
    /// Dump the equations after inlining (`.global.eqs`)
    GlobalEquations,
    LocalsGraph,
    /// Deprecated alias for `dump_call_only_flow`
    NonTransitiveGraph,
    /// Dump everything we know of
    All,
}

/// How a specific logging level was configured. (currently only used for the
/// `--debug` level)
#[derive(Debug, serde::Serialize, serde::Deserialize, Clone)]
pub enum LogLevelConfig {
    /// Logging for this level is only enabled for a specific target function
    Targeted(String),
    /// Logging for this level is not directly enabled
    Disabled,
    /// Logging for this level was directly enabled
    Enabled,
}

impl std::fmt::Display for LogLevelConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl LogLevelConfig {
    pub fn is_enabled(&self) -> bool {
        matches!(self, LogLevelConfig::Targeted(..) | LogLevelConfig::Enabled)
    }
}

impl Args {
    pub fn target(&self) -> Option<&str> {
        self.target.as_deref()
    }
    /// Returns the configuration specified for the `--debug` option
    pub fn debug(&self) -> &LogLevelConfig {
        &self.log_level_config
    }
    /// Access the debug arguments
    pub fn dbg(&self) -> &DumpArgs {
        &self.dump
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
    pub fn build_config(&self) -> &BuildConfig {
        &self.build_config
    }

    pub fn marker_control(&self) -> &MarkerControl {
        &self.marker_control
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
    /// example for the format can be generated by running `paralegal-flow` with
    /// `dump_serialized_flow_graph`.
    #[clap(long, env)]
    external_annotations: Option<std::path::PathBuf>,
}

impl ModelCtrl {
    pub fn external_annotations(&self) -> Option<&std::path::Path> {
        self.external_annotations.as_ref().map(|p| p.as_path())
    }
}

/// Arguments which control marker assignment and discovery
#[derive(serde::Serialize, serde::Deserialize, clap::Args)]
pub struct MarkerControl {
    /// Don't mark the outputs of local functions if they are of a marked type.
    ///
    /// Be aware that disabling this can cause unsoundness as inline
    /// construction of such types will not be emitted into the model. A warning
    /// is however emitted in that case.
    #[clap(long, env = "PARALEGAL_NO_LOCAL_FUNCTION_TYPE_MARKING")]
    no_local_function_type_marking: bool,
}

impl MarkerControl {
    pub fn local_function_type_marking(&self) -> bool {
        !self.no_local_function_type_marking
    }
}

/// Arguments that control the flow analysis
#[derive(serde::Serialize, serde::Deserialize, clap::Args)]
pub struct AnalysisCtrl {
    /// Disables all recursive analysis (both paralegal_flow's inlining as well as
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
    drop_clone: bool,
    #[clap(long, env)]
    drop_poll: bool,

    #[clap(long, env)]
    remove_poll_ctrl_influence: bool,

    #[clap(long, env)]
    inline_elision: bool,

    #[clap(long, env)]
    inline_no_arg_closures: bool,
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

    pub fn drop_clone(&self) -> bool {
        self.drop_clone
    }

    pub fn avoid_inlining(&self) -> bool {
        self.inline_elision
    }

    pub fn inline_no_arg_closures(&self) -> bool {
        self.inline_no_arg_closures
    }
}

impl DumpArgs {
    #[inline]
    fn has(&self, opt: DumpOption) -> bool {
        self.0.contains(DumpOption::All as u32).unwrap() || self.0.contains(opt as u32).unwrap()
    }
    pub fn dump_ctrl_mir(&self) -> bool {
        self.has(DumpOption::CtrlMir)
    }
    pub fn dump_serialized_non_transitive_graph(&self) -> bool {
        self.has(DumpOption::SerializedNonTransitiveGraph)
    }
    pub fn dump_call_only_flow(&self) -> bool {
        self.has(DumpOption::NonTransitiveGraph) || self.has(DumpOption::CallOnlyFlow)
    }
    pub fn dump_serialized_flow_graph(&self) -> bool {
        self.has(DumpOption::SerializedFlowGraph)
    }
    pub fn dump_dataflow_analysis_result(&self) -> bool {
        self.has(DumpOption::DataflowAnalysisResult)
    }
    pub fn dump_inlined_pruned_graph(&self) -> bool {
        self.has(DumpOption::InlinedPrunedGraph)
    }
    pub fn dump_inlined_graph(&self) -> bool {
        self.has(DumpOption::InlinedGraph)
    }
    pub fn dump_callee_mir(&self) -> bool {
        self.has(DumpOption::CalleeMir)
    }
    pub fn dump_pre_inline_graph(&self) -> bool {
        self.has(DumpOption::PreInlineGraph)
    }
    pub fn dump_regal_ir(&self) -> bool {
        self.has(DumpOption::RegalIr)
    }
    pub fn dump_local_equations(&self) -> bool {
        self.has(DumpOption::LocalEquations)
    }
    pub fn dump_global_equations(&self) -> bool {
        self.has(DumpOption::GlobalEquations)
    }
    pub fn dump_locals_graph(&self) -> bool {
        self.has(DumpOption::LocalsGraph)
    }
}

/// Dependency specific configuration
#[derive(serde::Serialize, serde::Deserialize, Default, Debug)]
pub struct DepConfig {
    /// Additional rust features to enable
    pub rust_features: Vec<String>,
}

/// Additional configuration for the build process/rustc
#[derive(serde::Deserialize, serde::Serialize, Default, Debug)]
pub struct BuildConfig {
    /// Dependency specific configuration
    pub dep: crate::HashMap<String, DepConfig>,
}
