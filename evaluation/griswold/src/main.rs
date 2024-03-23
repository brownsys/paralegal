use anyhow::Result;
use csv::Writer;
use paralegal_policy::paralegal_spdg::{Identifier, SPDGStats, SPDG};
use paralegal_policy::{Context, GraphLocation, SPDGGenCommand};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs::File;
use std::path::{Path, PathBuf};
use std::process::Child;
use std::sync::{self, Arc};
use std::thread;
use std::time::{Duration, Instant, SystemTime};

struct Run {
    compilation: &'static [&'static str],
    policies: fn(Arc<Context>) -> Result<()>,
}

#[derive(Serialize, Deserialize)]
struct RunStat {
    id: u32,
    experiment: String,
    policy: String,
    expectation: bool,
    result: Option<bool>,
    pdg_time: Duration,
    rustc_time: Option<Duration>,
    policy_time: Option<Duration>,
    deserialization_time: Option<Duration>,
    precomputation_time: Option<Duration>,
    traversal_time: Option<Duration>,
    num_controllers: Option<u16>,
    peak_mem_usage_pdg: u64,
    avg_mem_usage_pdg: u64,
    peak_cpu_usage_pdg: f32,
    avg_cpu_usage_pdg: f32,
    peak_mem_usage_policy: Option<u64>,
    avg_mem_usage_policy: Option<u64>,
    peak_cpu_usage_policy: Option<f32>,
    avg_cpu_usage_policy: Option<f32>,
}

impl RunStat {
    fn new(
        id: u32,
        experiment: String,
        policy: String,
        expectation: bool,
        pdg_stat: CmdStat,
    ) -> Self {
        Self {
            id,
            experiment,
            policy,
            expectation,
            result: None,
            pdg_time: pdg_stat.elapsed,
            rustc_time: None,
            policy_time: None,
            deserialization_time: None,
            precomputation_time: None,
            traversal_time: None,
            num_controllers: None,
            peak_cpu_usage_pdg: pdg_stat.peak_cpu,
            peak_cpu_usage_policy: None,
            avg_cpu_usage_pdg: pdg_stat.avg_cpu,
            avg_cpu_usage_policy: None,
            peak_mem_usage_pdg: pdg_stat.peak_mem,
            peak_mem_usage_policy: None,
            avg_mem_usage_pdg: pdg_stat.avg_mem,
            avg_mem_usage_policy: None,
        }
    }

    fn from_experiment(id: u32, exp: &Experiment, pdg_stat: CmdStat) -> Self {
        Self::new(
            id,
            exp.name(),
            exp.policy_name(),
            exp.expectation(),
            pdg_stat,
        )
    }

    fn add_policy_stat(
        &mut self,
        cmd_stat: CmdStat,
        ctx: &Context,
        success: bool,
        traversal_time: Duration,
    ) {
        macro_rules! set {
            ($field:ident, $target:expr) => {
                assert!(self.$field.replace($target).is_none());
            };
        }
        set!(avg_cpu_usage_policy, cmd_stat.avg_cpu);
        set!(peak_mem_usage_policy, cmd_stat.peak_mem);
        set!(precomputation_time, ctx.context_stats().precomputation);
        set!(result, success);
        set!(
            deserialization_time,
            ctx.context_stats().deserialization.unwrap()
        );
        set!(traversal_time, traversal_time);
        set!(num_controllers, ctx.desc().controllers.len() as u16);
        set!(rustc_time, ctx.desc().rustc_time);
    }
}

#[derive(Serialize, Deserialize)]
struct SysStat {
    num_cores: u16,
    num_physical_cores: u16,
    cpu_brand: String,
    cpu_frequency: u64,
    cpu_vendor_id: String,
    max_mem: u64,
    max_swap: u64,
    cpu_arch: Option<String>,
    kernel_version: Option<String>,
    os_version: Option<String>,
}

impl SysStat {
    fn new() -> Self {
        use sysinfo::System;
        let sys = System::new_all();
        let cpus = sys.cpus();
        let cpu = cpus.first().unwrap();
        let cpu_brand = cpu.brand().to_owned();
        let cpu_frequency = cpu.frequency();
        let cpu_vendor_id = cpu.vendor_id().to_owned();
        for cpu in cpus {
            assert_eq!(cpu_brand, cpu.brand());
            assert_eq!(cpu_frequency, cpu.frequency());
            assert_eq!(cpu_vendor_id, cpu.vendor_id());
        }
        Self {
            num_cores: cpus.len() as u16,
            num_physical_cores: sys.physical_core_count().unwrap() as u16,
            cpu_vendor_id,
            cpu_brand,
            cpu_frequency,
            max_mem: sys.total_memory(),
            max_swap: sys.total_swap(),
            cpu_arch: System::cpu_arch(),
            os_version: System::long_os_version(),
            kernel_version: System::kernel_version(),
        }
    }
}

#[derive(Serialize, Deserialize)]
struct ControllerStat {
    run_id: u32,
    name: Identifier,
    num_nodes: u32,
    #[serde(flatten)]
    statistics: SPDGStats,
    max_inlining_depth: u16,
    avg_inlining_depth: f32,
    num_edges: u32,
}

impl ControllerStat {
    fn from_spdg(run_id: u32, spdg: &SPDG) -> Self {
        let inlining_sum = spdg.graph.node_weights().map(|w| w.at.len()).sum::<usize>();
        Self {
            run_id,
            name: spdg.name,
            num_nodes: spdg.graph.node_count() as u32,
            statistics: spdg.statistics.clone(),
            max_inlining_depth: spdg.graph.node_weights().map(|w| w.at.len()).max().unwrap() as u16,
            avg_inlining_depth: inlining_sum as f32 / spdg.graph.node_count() as f32,
            num_edges: spdg.graph.edge_count() as u32,
        }
    }
}

#[derive(Serialize, Deserialize)]
struct Config {
    #[serde(with = "humantime_serde")]
    stat_refresh_interval: Duration,
    app_config: HashMap<Application, ApplicationConfig>,
    experiments: Box<[ExpVersion]>,
}

#[derive(Serialize, Deserialize)]
struct ApplicationConfig {
    source_dir: PathBuf,
}

#[derive(Serialize, Deserialize, strum::AsRefStr)]
#[serde(tag = "type", rename_all = "kebab-case")]
#[strum(serialize_all = "kebab-case")]
pub enum ExpVersion {
    RollForward(Application),
    Ablation,
    CaseStudies(Box<[Application]>),
    AdaptiveInlining(Application),
}

impl<'c> IntoIterator for &'c ExpVersion {
    type Item = Experiment<'c>;
    type IntoIter = Box<dyn Iterator<Item = Self::Item>>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            _ => unimplemented!(),
        }
    }
}

#[derive(Serialize, Deserialize, strum::AsRefStr, PartialEq, Eq, Hash)]
#[serde(rename_all = "kebab-case")]
#[strum(serialize_all = "kebab-case")]
pub enum Application {
    Plume,
    Lemmy,
    Hyperswitch,
    WebSubmit,
    AtomicData,
    Freedit,
}

impl Application {
    fn name(&self) -> &str {
        self.as_ref()
    }
}

pub struct Experiment<'c> {
    version: &'c ExpVersion,
    application: &'c Application,
    app_config: &'c ApplicationConfig,
    policy_name: &'c str,
    expectation: bool,
    prepare: Option<Box<dyn Fn()>>,
    policy: fn(Arc<Context>) -> anyhow::Result<()>,
}

impl Experiment<'_> {
    fn compile(&self) -> (SPDGGenCommand, &Path) {
        let cmd = SPDGGenCommand::global();

        (cmd, self.app_config.source_dir.as_path())
    }

    fn name(&self) -> String {
        format!("{}-{}", self.version.as_ref(), self.application.name())
    }

    fn policy_name(&self) -> String {
        self.policy_name.to_owned()
    }

    fn expectation(&self) -> bool {
        self.expectation
    }

    fn policy(&self) -> Box<dyn FnOnce(Arc<Context>) -> anyhow::Result<()>> {
        Box::new(self.policy)
    }
}

impl Config {
    fn experiments(&self) -> impl Iterator<Item = Experiment<'_>> {
        self.experiments.iter().flat_map(IntoIterator::into_iter)
    }
}

struct Output {
    controller_stat_out: Writer<File>,
    run_stat_out: Writer<File>,
}

impl Output {
    fn init() -> std::io::Result<Self> {
        let t = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        let general_output_dir: PathBuf = format!("run-{t}").into();
        let sys_stat = SysStat::new();
        let mut sys_stat_file = File::create(general_output_dir.join("sys.toml"))?;
        use std::io::Write;
        write!(
            sys_stat_file,
            "{}",
            toml::to_string_pretty(&sys_stat).unwrap()
        )
        .unwrap();
        Ok(Self {
            controller_stat_out: Writer::from_path(general_output_dir.join("controllers.csv"))?,
            run_stat_out: Writer::from_path(general_output_dir.join("results.csv"))?,
        })
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.controller_stat_out.flush()?;
        self.run_stat_out.flush()
    }
}

#[derive(Clone, Copy)]
struct CmdStat {
    peak_cpu: f32,
    avg_cpu: f32,
    peak_mem: u64,
    avg_mem: u64,
    elapsed: Duration,
}

impl CmdStat {
    fn for_self<R>(config: &Config, f: impl FnOnce() -> R) -> (R, Self) {
        thread::scope(|scope| {
            let sync = sync::OnceLock::new();

            let sync_clone = sync.clone();
            let handle = scope.spawn(|| {
                Self::collect(config, std::process::id(), move || {
                    sync_clone.get().is_some()
                })
            });

            let result = f();
            sync.set(()).unwrap();

            let stats = handle.join().unwrap();

            (result, stats)
        })
    }

    fn for_process(config: &Config, process: &mut Child) -> std::io::Result<Self> {
        let pid = process.id();
        let stat = Self::collect(config, pid, || process.try_wait().unwrap().is_some());

        Ok(stat)
    }

    fn collect(config: &Config, pid: u32, mut poll: impl FnMut() -> bool) -> Self {
        let mut sys_stat = sysinfo::System::new();
        let pid = sysinfo::Pid::from_u32(pid);
        let mut sum_mem = 1;
        let mut num_samples = 0;
        let mut sum_cpu = 0.0_f32;
        let mut peak_cpu = 0.0_f32;
        let mut peak_mem = 0;
        let started = Instant::now();

        while !poll() {
            std::thread::sleep(config.stat_refresh_interval);
            sys_stat.refresh_process(pid);
            if let Some(proc_info) = sys_stat.process(pid) {
                peak_mem = peak_mem.max(proc_info.memory());
                sum_mem += proc_info.memory();
                sum_cpu += proc_info.cpu_usage();
                peak_cpu = peak_cpu.max(proc_info.cpu_usage());
                num_samples += 1;
            }
        }

        CmdStat {
            peak_cpu,
            peak_mem,
            avg_cpu: sum_cpu / num_samples as f32,
            avg_mem: sum_mem / num_samples,
            elapsed: started.elapsed(),
        }
    }
}

fn main() {
    let mut output = Output::init().unwrap();
    let config_file = std::fs::read_to_string("bench-config.toml").unwrap();
    let config: Config = toml::from_str(&config_file).unwrap();

    for (id, exp) in config.experiments().enumerate() {
        if let Some(prepare) = exp.prepare.as_ref() {
            (prepare)()
        }
        let (mut compile_command, compile_dir) = exp.compile();
        let mut process = compile_command.get_command().spawn().unwrap();
        let cmd_stat = CmdStat::for_process(&config, &mut process).unwrap();
        let mut run_stats = RunStat::from_experiment(id as u32, &exp, cmd_stat);
        if process.try_wait().unwrap().unwrap().success() {
            let policy = exp.policy();
            let ((ctx, success, traversal_time), cmd_stat) = CmdStat::for_self(&config, || {
                let ctx = Arc::new(
                    GraphLocation::std(compile_dir)
                        .build_context(paralegal_policy::Config::default())
                        .unwrap(),
                );
                let policy_start = Instant::now();
                (policy)(ctx.clone()).unwrap();
                let success = ctx.emit_diagnostics(std::io::stdout()).unwrap();
                (ctx, success, policy_start.elapsed())
            });
            run_stats.add_policy_stat(cmd_stat, ctx.as_ref(), success, traversal_time);
            for ctrl in ctx.desc().controllers.values() {
                output
                    .controller_stat_out
                    .serialize(ControllerStat::from_spdg(id as u32, ctrl))
                    .unwrap()
            }
        } else {
            println!(
                "WARNING: Run id {} dir not successfully pass PDG construction",
                id
            );
        }
        output.run_stat_out.serialize(run_stats).unwrap();
        output.flush().unwrap();
    }
}
