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

// Unfortunately we have to do this, because num-traits::FromPrimitive generates
// code that triggers this lint
#![allow(non_local_definitions)]

use anyhow::Error;
use clap::ValueEnum;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::OnceLock;

use cargo_paralegal_flow::{
    ClapAnalysisCtrl, ClapArgs, Debugger, DumpOption, MarkerControl, ParseableDumpArgs,
};
use flowistry_pdg_construction::source_access::std_crates;
use paralegal_spdg::utils::setup_logging;

use crate::utils::TinyBitSet;

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
        let build_config: (_, BuildConfig) = if let Some(conf) = value.get_build_config() {
            let absolute = conf.canonicalize()?;
            let config = toml::from_str(&std::fs::read_to_string(&absolute)?)?;
            (Some(absolute), config)
        } else {
            Default::default()
        };
        let ClapArgs {
            result_path,
            relaxed,
            target,
            abort_after_analysis,
            mut anactrl,
            dump,
            marker_control,
            cargo_args,
            attach_to_debugger,
            strict,
            build_config: _,
            forward_json: _,
        } = value;
        if relaxed {
            eprintln!(
                "The `--relaxed` flag is deprecated. This is now the default behavior and therefore the flag is ignored."
            );
        }
        let mut dump: DumpArgs = dump.into();
        if let Some(from_env) = env_var_expect_unicode("PARALEGAL_DUMP")? {
            let from_env = DumpArgs::from_str(&from_env).map_err(|s| anyhow::anyhow!("{}", s))?;
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

        anactrl
            .include
            .extend(build_config.1.include.iter().cloned());

        Ok(Args {
            result_path,
            relaxed: !strict,
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

pub struct Args {
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
            result_path: PathBuf::from(paralegal_spdg::FLOW_GRAPH_OUT_NAME),
            relaxed: true,
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

impl From<DumpOption> for DumpArgs {
    fn from(value: DumpOption) -> Self {
        [value].into_iter().collect()
    }
}

impl From<ParseableDumpArgs> for DumpArgs {
    fn from(value: ParseableDumpArgs) -> Self {
        value.dump.into_iter().collect()
    }
}

/// Collection of the [`DumpOption`]s a user has set.
///
/// Separates the cli and the internal api. Users set [`DumpOption`]s in the
/// cli, internally we use the snake-case version of the option as a method on
/// this type. This is so we can rename the outer UI without breaking code or
/// even combine options together.
#[derive(Clone, Default)]
pub struct DumpArgs(TinyBitSet);

impl FromStr for DumpArgs {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.split(",")
            .map(|opt| DumpOption::from_str(opt, true))
            .collect()
    }
}

impl FromIterator<DumpOption> for DumpArgs {
    fn from_iter<T: IntoIterator<Item = DumpOption>>(iter: T) -> Self {
        Self(iter.into_iter().map(|v| v as u32).collect())
    }
}
impl Args {
    pub fn target(&self) -> Option<&str> {
        self.target.as_deref()
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

    pub fn marker_control(&self) -> &MarkerControl {
        &self.marker_control
    }

    pub fn cargo_args(&self) -> &[String] {
        &self.cargo_args
    }

    pub fn attach_to_debugger(&self) -> Option<Debugger> {
        self.attach_to_debugger
    }

    pub fn setup_logging(&self) -> anyhow::Result<()> {
        setup_logging()
    }
}

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
    included_crate_cache: OnceLock<FxHashSet<CrateNum>>,
    no_pdg_cache: bool,
    include_std: bool,
    fail_on_deep_call_chain: Option<u32>,
}

impl std::hash::Hash for AnalysisCtrl {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let Self {
            analyze,
            inlining_depth,
            include,
            included_crate_cache: _,
            no_pdg_cache,
            include_std,
            fail_on_deep_call_chain
        } = self;
        analyze.hash(state);
        inlining_depth.hash(state);
        include.hash(state);
        no_pdg_cache.hash(state);
        include_std.hash(state);
        fail_on_deep_call_chain.hash(state);
    }
}

impl Default for AnalysisCtrl {
    fn default() -> Self {
        Self {
            analyze: Vec::new(),
            inlining_depth: InliningDepth::Adaptive(0),
            include: Default::default(),
            no_pdg_cache: false,
            included_crate_cache: OnceLock::new(),
            include_std: false,
            fail_on_deep_call_chain: None,
        }
    }
}

impl TryFrom<ClapAnalysisCtrl> for AnalysisCtrl {
    type Error = Error;
    fn try_from(value: ClapAnalysisCtrl) -> Result<Self, Self::Error> {
        let ClapAnalysisCtrl {
            analyze,
            include,
            no_pdg_cache,
            no_interprocedural_analysis,
            no_adaptive_approximation,
            k_depth,
            include_std,
            fail_on_deep_call_chain
        } = value;

        let inlining_depth = if no_interprocedural_analysis {
            InliningDepth::K(0)
        } else if no_adaptive_approximation {
            k_depth.map_or(InliningDepth::Unconstrained, InliningDepth::K)
        } else {
            InliningDepth::Adaptive(k_depth.unwrap_or(0))
        };

        Ok(Self {
            analyze,
            inlining_depth,
            include,
            no_pdg_cache,
            included_crate_cache: OnceLock::new(),
            include_std,
            fail_on_deep_call_chain
        })
    }
}

#[derive(strum::EnumIs, strum::AsRefStr, Clone, Hash)]
pub enum InliningDepth {
    /// Inline to arbitrary depth
    Unconstrained,
    /// Perform inlining until depth k
    K(u32),
    /// Inline so long as markers are reachable + k steps
    Adaptive(u32),
}

impl AnalysisCtrl {
    /// Externally (via command line) selected analysis targets
    pub fn selected_targets(&self) -> &[String] {
        &self.analyze
    }

    /// Are we recursing into (unmarked) called functions with the analysis?
    pub fn use_recursive_analysis(&self) -> bool {
        !matches!(self.inlining_depth, InliningDepth::K(0))
    }

    pub fn inlining_depth(&self) -> &InliningDepth {
        &self.inlining_depth
    }

    pub fn included(&self, crate_name: &str) -> bool {
        if self.include.is_empty() {
            true
        } else {
            self.include.iter().any(|s| s == crate_name)
        }
    }

    fn crate_inclusion_set<'a>(&'a self, tcx: TyCtxt<'_>) -> &'a FxHashSet<CrateNum> {
        self.included_crate_cache
            .get_or_init(|| {
                if self.include.is_empty() {
                    let std_crates = if self.include_std {
                        Default::default()
                    } else {
                        std_crates(tcx).collect::<FxHashSet<_>>()
                    };
                    tcx.crates(())
                        .iter()
                        .copied()
                        .filter(move |c| !std_crates.contains(c))
                        .chain([LOCAL_CRATE])
                        .collect()
                } else {
                    let mut included_crate_names = self
                        .include
                        .iter()
                        // "--include=crate" can be used to force only the local crate
                        // to be included.
                        .filter(|c| c.as_str() != "crate")
                        .map(|s| (Symbol::intern(s), false))
                        .collect::<FxHashMap<_, bool>>();
                    let set = tcx.crates(())
                        .iter()
                        .copied()
                        .filter(|cnum| included_crate_names.get_mut(&tcx.crate_name(*cnum)).is_some_and(|v| {
                            *v = true;
                            true
                        }))
                        .chain([LOCAL_CRATE])
                        .collect();
                    for (k, v) in included_crate_names {
                        if !v {
                            tcx.dcx().warn(format!("The crate `{k}` was configured for inclusion but is not part of the dependencies."));
                        }
                    }
                    set
                }
            })
    }

    pub fn included_crates<'a>(&'a self, tcx: TyCtxt<'_>) -> impl Iterator<Item = CrateNum> + 'a {
        self.crate_inclusion_set(tcx).iter().copied()
    }

    pub fn inclusion_predicate(&self, tcx: TyCtxt<'_>) -> impl Fn(CrateNum) -> bool {
        let included_crates = self.crate_inclusion_set(tcx).clone();
        move |cnum| included_crates.contains(&cnum)
    }

    pub fn pdg_cache(&self) -> bool {
        !self.no_pdg_cache
    }

    pub fn include_std(&self) -> bool {
        self.include_std
    }

    pub fn fail_on_deep_call_chain(&self) -> Option<u32> {
        self.fail_on_deep_call_chain
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
#[serde(deny_unknown_fields)]
pub struct DepConfig {
    #[serde(default, alias = "rust-features")]
    /// Additional rust features to enable
    pub rust_features: Box<[String]>,
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
#[serde(tag = "mode", rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
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
#[serde(deny_unknown_fields)]
pub struct BuildConfig {
    /// Dependency specific configuration
    #[serde(default)]
    pub dep: BTreeMap<String, DepConfig>,
    /// A select list of non-workspace crates which should be recursed into
    /// during analysis. If you want this to happen for all non-workspace crates
    /// instead specify `default-include = true`.
    #[serde(default)]
    pub include: Vec<String>,
    #[serde(default)]
    pub stubs: BTreeMap<String, Stub>,
}
