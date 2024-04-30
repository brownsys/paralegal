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
use std::ffi::{OsStr, OsString};

use crate::utils::TinyBitSet;
use crate::{num_derive, num_traits::FromPrimitive};

#[derive(thiserror::Error, Debug)]
enum VarError {
    #[error("env variable value is not unicode, approximate key and value are {}: {}", key.to_string_lossy(), value.to_string_lossy())]
    NotUnicode { key: OsString, value: OsString },
}

/// A thin wrapper around `std::env::var` that returns `None` if the variable is
/// not present.
fn env_var_expect_unicode(k: impl AsRef<OsStr>) -> Result<Option<String>, VarError> {
    let k_ref = k.as_ref();
    match std::env::var(k_ref) {
        Ok(v) => Ok(Some(v)),
        Err(std::env::VarError::NotUnicode(u)) => Err(VarError::NotUnicode {
            key: k_ref.to_owned(),
            value: u,
        }),
        Err(std::env::VarError::NotPresent) => Ok(None),
    }
}

impl TryFrom<ClapArgs> for Args {
    type Error = Error;
    fn try_from(value: ClapArgs) -> Result<Self, Self::Error> {
        let ClapArgs {
            verbose,
            debug,
            debug_target,
            result_path,
            relaxed,
            target,
            abort_after_analysis,
            mut anactrl,
            modelctrl,
            dump,
            marker_control,
            cargo_args,
            trace,
        } = value;
        let mut dump: DumpArgs = dump.into();
        if let Some(from_env) = env_var_expect_unicode("PARALEGAL_DUMP")? {
            let from_env =
                DumpArgs::from_str(&from_env, false).map_err(|s| anyhow::anyhow!("{}", s))?;
            dump.0 |= from_env.0;
        }
        anactrl.analyze = anactrl
            .analyze
            .iter()
            .flat_map(|s| s.split(',').map(ToOwned::to_owned))
            .collect();
        if let Some(from_env) = env_var_expect_unicode("PARALEGAL_ANALYZE")? {
            anactrl
                .analyze
                .extend(from_env.split(',').map(ToOwned::to_owned));
        }
        let build_config_file = std::path::Path::new("Paralegal.toml");
        let build_config = if build_config_file.exists() {
            toml::from_str(&std::fs::read_to_string(build_config_file)?)?
        } else {
            Default::default()
        };
        let log_level_config = match debug_target {
            Some(target) if !target.is_empty() => LogLevelConfig::Targeted(target),
            _ => LogLevelConfig::Disabled,
        };
        let verbosity = if trace {
            log::LevelFilter::Trace
        } else if debug {
            log::LevelFilter::Debug
        } else if verbose {
            log::LevelFilter::Info
        } else {
            log::LevelFilter::Warn
        };
        Ok(Args {
            verbosity,
            log_level_config,
            result_path,
            relaxed,
            target,
            abort_after_analysis,
            anactrl: anactrl.try_into()?,
            modelctrl,
            dump,
            build_config,
            marker_control,
            cargo_args,
        })
    }
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct Args {
    /// Print additional logging output (up to the "info" level)
    verbosity: log::LevelFilter,
    log_level_config: LogLevelConfig,
    /// Where to write the resulting forge code to (defaults to `analysis_result.frg`)
    result_path: std::path::PathBuf,
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
    /// Additional options for cargo
    cargo_args: Vec<String>,
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
    #[clap(long, env = "PARALEGAL_TRACE")]
    trace: bool,
    #[clap(long, env = "PARALEGAL_DEBUG_TARGET")]
    debug_target: Option<String>,
    /// Where to write the resulting GraphLocation (defaults to `flow-graph.json`)
    #[clap(long, default_value = paralegal_spdg::FLOW_GRAPH_OUT_NAME)]
    result_path: std::path::PathBuf,
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
    anactrl: ClapAnalysisCtrl,
    /// Additional arguments which control marker assignment and discovery
    #[clap(flatten, next_help_heading = "Marker Control")]
    marker_control: MarkerControl,
    /// Additional arguments that control the generation and composition of the model
    #[clap(flatten, next_help_heading = "Model Generation")]
    modelctrl: ModelCtrl,
    /// Additional arguments that control debug args specifically
    #[clap(flatten)]
    dump: ParseableDumpArgs,
    /// Pass through for additional cargo arguments (like --features)
    #[clap(last = true)]
    cargo_args: Vec<String>,
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
    /// A simple PDG rendering per controller provided by flowistry
    FlowistryPdg,
    /// A PDG rendering that includes markers and is grouped by call site.
    /// Includes all controllers that are analyzed.
    Spdg,
    /// Dump the MIR (`.mir`) of each called controller
    Mir,
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
}

impl LogLevelConfig {
    pub fn is_enabled(&self) -> bool {
        matches!(self, LogLevelConfig::Targeted(_))
    }
}

impl std::fmt::Display for LogLevelConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl Args {
    pub fn target(&self) -> Option<&str> {
        self.target.as_deref()
    }
    /// Returns the configuration specified for the `--debug` option
    pub fn direct_debug(&self) -> &LogLevelConfig {
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
    pub fn verbosity(&self) -> log::LevelFilter {
        self.verbosity
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

    pub fn cargo_args(&self) -> &[String] {
        &self.cargo_args
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
        self.external_annotations.as_deref()
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
#[derive(clap::Args)]
struct ClapAnalysisCtrl {
    /// Target this function as analysis target. Command line version of
    /// `#[paralegal::analyze]`). Must be a full rust path and resolve to a
    /// function. May be specified multiple times and multiple, comma separated
    /// paths may be supplied at the same time.
    #[clap(long)]
    analyze: Vec<String>,
    /// Disables all recursive analysis (both paralegal_flow's inlining as well as
    /// Flowistry's recursive analysis).
    #[clap(long, env)]
    no_cross_function_analysis: bool,
    /// Generate PDGs that span all called functions which can attach markers
    #[clap(long, conflicts_with_all = ["fixed_depth", "unconstrained_depth", "no_cross_function_analysis"])]
    adaptive_depth: bool,
    /// Generate PDGs that span functions up to a certain depth
    #[clap(long, conflicts_with_all = ["adaptive_depth", "unconstrained_depth", "no_cross_function_analysis"])]
    fixed_depth: Option<u8>,
    /// Generate PDGs that span to all functions for which we have source code.
    ///
    /// If no depth option is specified this is the default right now but that
    /// is not guaranteed to be the case in the future. If you want to guarantee
    /// this is used explicitly supply the argument.
    #[clap(long, conflicts_with_all = ["fixed_depth", "adaptive_depth", "no_cross_function_analysis"])]
    unconstrained_depth: bool,
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct AnalysisCtrl {
    /// Target this function as analysis target. Command line version of
    /// `#[paralegal::analyze]`). Must be a full rust path and resolve to a
    /// function. May be specified multiple times and multiple, comma separated
    /// paths may be supplied at the same time.
    analyze: Vec<String>,
    /// Disables all recursive analysis (both paralegal_flow's inlining as well as
    /// Flowistry's recursive analysis).
    inlining_depth: InliningDepth,
}

impl TryFrom<ClapAnalysisCtrl> for AnalysisCtrl {
    type Error = Error;
    fn try_from(value: ClapAnalysisCtrl) -> Result<Self, Self::Error> {
        let ClapAnalysisCtrl {
            analyze,
            no_cross_function_analysis,
            adaptive_depth,
            fixed_depth,
            unconstrained_depth: _,
        } = value;

        let inlining_depth = if adaptive_depth {
            InliningDepth::Adaptive
        } else if let Some(n) = fixed_depth {
            InliningDepth::Fixed(n)
        } else if no_cross_function_analysis {
            InliningDepth::Fixed(0)
        } else {
            InliningDepth::Unconstrained
        };

        Ok(Self {
            analyze,
            inlining_depth,
        })
    }
}

#[derive(serde::Serialize, serde::Deserialize, strum::EnumIs, strum::AsRefStr, Clone)]
pub enum InliningDepth {
    /// Inline to arbitrary depth
    Unconstrained,
    /// Inline to a depth of `n` and no further
    Fixed(u8),
    /// Inline so long as markers are reachable
    Adaptive,
}

impl AnalysisCtrl {
    /// Externally (via command line) selected analysis targets
    pub fn selected_targets(&self) -> &[String] {
        &self.analyze
    }

    /// Are we recursing into (unmarked) called functions with the analysis?
    pub fn use_recursive_analysis(&self) -> bool {
        !matches!(self.inlining_depth, InliningDepth::Fixed(0))
    }

    pub fn inlining_depth(&self) -> &InliningDepth {
        &self.inlining_depth
    }
}

impl DumpArgs {
    #[inline]
    fn has(&self, opt: DumpOption) -> bool {
        self.0.contains(DumpOption::All as u32).unwrap() || self.0.contains(opt as u32).unwrap()
    }

    pub fn dump_flowistry_pdg(&self) -> bool {
        self.has(DumpOption::FlowistryPdg)
    }

    pub fn dump_spdg(&self) -> bool {
        self.has(DumpOption::Spdg)
    }

    pub fn dump_mir(&self) -> bool {
        self.has(DumpOption::Mir)
    }
}

/// Dependency specific configuration
#[derive(serde::Serialize, serde::Deserialize, Default, Debug)]
pub struct DepConfig {
    #[serde(default)]
    /// Additional rust features to enable
    pub rust_features: Box<[String]>,
}

/// Additional configuration for the build process/rustc
#[derive(serde::Deserialize, serde::Serialize, Default, Debug)]
pub struct BuildConfig {
    /// Dependency specific configuration
    pub dep: crate::HashMap<String, DepConfig>,
}
