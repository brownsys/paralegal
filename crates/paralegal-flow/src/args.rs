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
use std::collections::HashMap;
use std::ffi::{OsStr, OsString};
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

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
            dump,
            marker_control,
            cargo_args,
            trace,
            attach_to_debugger,
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
        let build_config: (_, BuildConfig) = if let Ok(absolute) = build_config_file.canonicalize()
        {
            let config = toml::from_str(&std::fs::read_to_string(&absolute)?)?;
            (Some(absolute), config)
        } else {
            Default::default()
        };
        anactrl
            .include
            .extend(build_config.1.include.iter().cloned());
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
            dump,
            build_config,
            marker_control,
            cargo_args,
            attach_to_debugger,
        })
    }
}

#[derive(serde::Serialize, serde::Deserialize, clap::ValueEnum, Clone, Copy)]
pub enum Debugger {
    /// The CodeLLDB debugger. Learn more at <https://github.com/vadimcn/codelldb/blob/v1.10.0/MANUAL.md>.
    CodeLldb,
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
    /// Target a specific package
    target: Option<String>,
    /// Abort the compilation after finishing the analysis
    abort_after_analysis: bool,
    /// Make the compiler attach to a debugger
    attach_to_debugger: Option<Debugger>,
    /// Additional arguments on marker assignment and discovery
    marker_control: MarkerControl,
    /// Additional arguments that control the flow analysis specifically
    anactrl: AnalysisCtrl,
    /// Additional arguments that control debug output specifically
    dump: DumpArgs,
    /// Additional configuration for the build process/rustc
    build_config: (Option<PathBuf>, BuildConfig),
    /// Additional options for cargo
    cargo_args: Vec<String>,
}

impl Default for Args {
    fn default() -> Self {
        Self {
            verbosity: log::LevelFilter::Info,
            log_level_config: LogLevelConfig::Disabled,
            result_path: PathBuf::from(paralegal_spdg::FLOW_GRAPH_OUT_NAME),
            relaxed: false,
            target: None,
            abort_after_analysis: false,
            marker_control: Default::default(),
            anactrl: Default::default(),
            dump: Default::default(),
            build_config: Default::default(),
            cargo_args: Vec::new(),
            attach_to_debugger: None,
        }
    }
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
    /// Run paralegal only on this crate
    #[clap(long, env = "PARALEGAL_TARGET")]
    target: Option<String>,
    /// Abort the compilation after finishing the analysis
    #[clap(long, env)]
    abort_after_analysis: bool,
    /// Attach to a debugger before running the analyses
    #[clap(long)]
    attach_to_debugger: Option<Debugger>,
    /// Additional arguments that control the flow analysis specifically
    #[clap(flatten, next_help_heading = "Flow Analysis")]
    anactrl: ClapAnalysisCtrl,
    /// Additional arguments which control marker assignment and discovery
    #[clap(flatten, next_help_heading = "Marker Control")]
    marker_control: MarkerControl,
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
#[derive(serde::Serialize, serde::Deserialize, Clone, Default)]
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
        &self.build_config.1
    }

    pub fn hash_config(&self, hasher: &mut impl Hasher) {
        if self.attach_to_debugger.is_some() {
            // If we run the debugger try to make the hash fail so we actually run.
            std::time::Instant::now().hash(hasher);
        }
        // TODO Add other relevant arguments
        config_hash_for_file(&self.build_config.0, hasher);
        self.relaxed.hash(hasher);
        self.target.hash(hasher);
        self.result_path.hash(hasher);
        config_hash_for_file(&self.marker_control.external_annotations, hasher);
    }

    pub fn marker_control(&self) -> &MarkerControl {
        &self.marker_control
    }

    pub fn cargo_args(&self) -> &[String] {
        &self.cargo_args
    }

    pub fn attach_to_debugger(&self) -> Option<Debugger> {
        self.attach_to_debugger
    }

    pub fn setup_logging(&self) {
        let lvl = self.verbosity();
        // //let lvl = log::LevelFilter::Debug;
        if simple_logger::SimpleLogger::new()
            .with_level(lvl)
            .with_module_level("flowistry", lvl)
            .with_module_level("rustc_utils", log::LevelFilter::Error)
            .without_timestamps()
            .init()
            .is_ok()
            && matches!(*self.direct_debug(), LogLevelConfig::Targeted(..))
        {
            log::set_max_level(log::LevelFilter::Warn);
        }
    }
}

fn config_hash_for_file(path: &Option<impl AsRef<Path>>, state: &mut impl Hasher) {
    path.as_ref()
        .map(|path| {
            let path = path.as_ref();
            Ok::<_, std::io::Error>((path, path.metadata()?.modified()?))
        })
        .transpose()
        .unwrap()
        .hash(state);
}

#[derive(serde::Serialize, serde::Deserialize, clap::Args, Default)]
pub struct MarkerControl {
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

impl MarkerControl {
    pub fn external_annotations(&self) -> Option<&std::path::Path> {
        self.external_annotations.as_deref()
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
    #[clap(long, conflicts_with_all = ["unconstrained_depth", "no_cross_function_analysis"])]
    adaptive_depth: bool,
    /// Generate PDGs that span to all functions for which we have source code.
    ///
    /// If no depth option is specified this is the default right now but that
    /// is not guaranteed to be the case in the future. If you want to guarantee
    /// this is used explicitly supply the argument.
    #[clap(long, conflicts_with_all = ["adaptive_depth", "no_cross_function_analysis"])]
    unconstrained_depth: bool,
    /// Crates that should be recursed into.
    #[clap(long)]
    include: Vec<String>,
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
    include: Vec<String>,
}

impl Default for AnalysisCtrl {
    fn default() -> Self {
        Self {
            analyze: Vec::new(),
            inlining_depth: InliningDepth::Adaptive,
            include: Default::default(),
        }
    }
}

impl TryFrom<ClapAnalysisCtrl> for AnalysisCtrl {
    type Error = Error;
    fn try_from(value: ClapAnalysisCtrl) -> Result<Self, Self::Error> {
        let ClapAnalysisCtrl {
            analyze,
            no_cross_function_analysis,
            adaptive_depth,
            unconstrained_depth: _,
            include,
        } = value;

        let inlining_depth = if adaptive_depth {
            InliningDepth::Adaptive
        } else if no_cross_function_analysis {
            InliningDepth::Shallow
        } else {
            InliningDepth::Unconstrained
        };

        Ok(Self {
            analyze,
            inlining_depth,
            include,
        })
    }
}

#[derive(serde::Serialize, serde::Deserialize, strum::EnumIs, strum::AsRefStr, Clone)]
pub enum InliningDepth {
    /// Inline to arbitrary depth
    Unconstrained,
    /// Perform no inlining
    Shallow,
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
        !matches!(self.inlining_depth, InliningDepth::Shallow)
    }

    pub fn inlining_depth(&self) -> &InliningDepth {
        &self.inlining_depth
    }

    pub fn included(&self) -> &[String] {
        &self.include
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
    #[serde(default, alias = "rust-features")]
    /// Additional rust features to enable
    pub rust_features: Box<[String]>,
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
#[serde(tag = "mode", rename_all = "kebab-case")]
pub enum Stub {
    #[serde(rename_all = "kebab-case")]
    /// Replaces the result of a call to a higher-order function with a call to
    /// the input closure.
    SubClosure { generic_name: String },
    #[serde(rename_all = "kebab-case")]
    /// Replaces the result of a higher-order future by an input future.
    SubFuture { generic_name: String },
}

/// Additional configuration for the build process/rustc
#[derive(serde::Deserialize, serde::Serialize, Default, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct BuildConfig {
    /// Dependency specific configuration
    #[serde(default)]
    pub dep: crate::HashMap<String, DepConfig>,
    #[serde(default)]
    pub include: Vec<String>,
    #[serde(default)]
    pub stubs: HashMap<String, Stub>,
}
