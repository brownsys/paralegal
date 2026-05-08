use std::{
    hash::{Hash, Hasher},
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};

pub const PARALEGAL_ARGS: &str = "PARALEGAL_ARGS";

pub const EXEC_HASH_ARG: &str = "--exec-hash";

/// Arguments as exposed on the command line.
///
/// You should then use `try_into` to convert this to [`Args`], the argument
/// structure used internally.
#[derive(clap::Parser, Serialize, Deserialize)]
pub struct ClapArgs {
    /// Where to write the resulting GraphLocation (defaults to `flow-graph.json`)
    #[clap(long, default_value = paralegal_non_rustc_utils::FLOW_GRAPH_OUT_NAME)]
    pub result_path: std::path::PathBuf,
    /// Emit warnings instead of aborting the analysis on sanity checks
    ///
    /// This is now the default behavior and this flag is deprecated. Use
    /// `--strict` to turn off this behavior.
    #[clap(long, env = "PARALEGAL_RELAXED", hide = true)]
    pub relaxed: bool,
    /// Emit errors instead of warnings for potential soundness risks
    #[clap(long, env = "PARALEGAL_STRICT")]
    pub strict: bool,
    /// Run paralegal only on this crate
    #[clap(long, env = "PARALEGAL_TARGET")]
    pub target: Option<String>,
    /// Abort the compilation after finishing the analysis
    #[clap(long, env)]
    pub abort_after_analysis: bool,
    /// Attach to a debugger before running the analyses
    #[clap(long)]
    pub attach_to_debugger: Option<Debugger>,
    /// Additional arguments that control the flow analysis specifically
    #[clap(flatten, next_help_heading = "Flow Analysis")]
    pub anactrl: ClapAnalysisCtrl,
    /// Additional arguments which control marker assignment and discovery
    #[clap(flatten, next_help_heading = "Marker Control")]
    pub marker_control: MarkerControl,
    /// Additional arguments that control debug args specifically
    #[clap(flatten)]
    pub dump: ParseableDumpArgs,
    /// Pass through for additional cargo arguments (like --features)
    #[clap(long)]
    pub build_config: Option<PathBuf>,
    /// When set, forward raw cargo JSON/text lines to stdout unmodified.
    /// This makes `cargo-paralegal-flow` act more like a drop-in replacement
    /// for `cargo` when tools expect `--message-format=json` output.
    #[clap(long)]
    pub forward_json: bool,
    #[clap(last = true)]
    pub cargo_args: Vec<String>,
}

impl ClapArgs {
    pub fn hash_config(&self, hasher: &mut impl Hasher) {
        if self.attach_to_debugger.is_some() {
            // If we run the debugger try to make the hash fail so we actually run.
            std::time::Instant::now().hash(hasher);
        }
        // TODO Add other relevant arguments
        let build_config = self.get_build_config();
        config_hash_for_file(build_config, hasher);
        self.relaxed.hash(hasher);
        self.target.hash(hasher);
        self.result_path.hash(hasher);
        config_hash_for_file(self.marker_control.external_annotations().as_ref(), hasher);
    }

    pub fn get_build_config(&self) -> Option<&Path> {
        const DEFAULT_BUILD_CONFIG_PATH: &str = "Paralegal.toml";
        self.build_config.as_deref().or_else(|| {
            let path = Path::new(DEFAULT_BUILD_CONFIG_PATH);
            path.exists().then_some(path)
        })
    }
}

pub fn config_hash_for_file(path: Option<impl AsRef<Path>>, state: &mut impl Hasher) {
    path.as_ref()
        .map(|path| {
            let path = path.as_ref();
            Ok::<_, std::io::Error>((path, path.metadata()?.modified()?))
        })
        .transpose()
        .unwrap()
        .hash(state);
}

#[derive(serde::Serialize, serde::Deserialize, clap::ValueEnum, Clone, Copy)]
pub enum Debugger {
    /// The CodeLLDB debugger. Learn more at <https://github.com/vadimcn/codelldb/blob/v1.10.0/MANUAL.md>.
    CodeLldb,
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
pub enum DumpOption {
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

#[derive(Clone, clap::Args, Serialize, Deserialize)]
pub struct ParseableDumpArgs {
    /// Generate intermediate of various formats and at various stages of
    /// compilation. A short description of each value is provided here, for a
    /// more comprehensive explanation refer to the [notion page on
    /// dumping](https://www.notion.so/justus-adam/Dumping-Intermediate-Representations-4bd66ec11f8f4c459888a8d8cfb10e93).
    ///
    /// Can also be supplied as a comma-separated list (no spaces) and be set with the `PARALEGAL_DUMP` variable.
    #[clap(long, value_enum)]
    pub dump: Vec<DumpOption>,
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

    /// Whether to automatically mark possibly side-effecting functions.
    ///
    /// Implies `--include-std`.
    #[clap(long, env)]
    side_effect_markers: bool,
    #[clap(long)]
    elide_on_whitelist_markers: bool,
}

/// Arguments that control the flow analysis
#[derive(clap::Args, Serialize, Deserialize)]
pub struct ClapAnalysisCtrl {
    /// Target this function as analysis entrypoint. Command line version of
    /// `#[paralegal::analyze]`). Must be a full rust path and resolve to a
    /// function. May be specified multiple times and multiple, comma separated
    /// paths may be supplied at the same time.
    #[clap(long)]
    pub analyze: Vec<String>,
    /// Limits the PDG to a single function. This is intended for testing and
    /// should not be used in production.
    #[clap(long, env)]
    pub no_interprocedural_analysis: bool,
    /// Do not decide whether to represent a function in the PDG based on the
    /// presence of markers. This will create very large PDGs that span all
    /// crates configured for analysis and with source code present.
    #[clap(long, conflicts_with_all = ["no_interprocedural_analysis"])]
    pub no_adaptive_approximation: bool,
    /// Limit the set of crates to analyze. Beware that if those crates contain
    /// marked code (other than the surface API), this poses a soundness risk.
    /// This is intended as an optimization experts can apply for large
    /// projects.
    #[clap(long)]
    pub include: Vec<String>,
    #[clap(long)]
    pub no_pdg_cache: bool,
    /// Add an additional k inlining steps on top of what the marker guided
    /// setup recommends. If adaptive approximation is enabled this defaults to
    /// 0, if it is enabled it defaults to no limit.
    #[clap(long, conflicts_with = "no_interprocedural_analysis")]
    pub k_depth: Option<u32>,
    /// Recompile the standard library and make the code available for analysis.
    #[clap(long, env)]
    pub include_std: bool,
}

impl MarkerControl {
    pub fn external_annotations(&self) -> Option<&std::path::Path> {
        self.external_annotations.as_deref()
    }

    pub fn mark_side_effects(&self) -> bool {
        self.side_effect_markers
    }

    pub fn elide_on_whitelist_markers(&self) -> bool {
        self.elide_on_whitelist_markers
    }
}
