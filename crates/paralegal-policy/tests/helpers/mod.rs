use std::{
    collections::hash_map::DefaultHasher, env, fs::File, hash::Hash, io, path::PathBuf,
    process::Command, sync::Arc, time::SystemTime,
};

pub use anyhow::{ensure, Result};

use paralegal_policy::{Context, GraphLocation};

fn temporary_directory() -> Result<PathBuf> {
    let tmpdir = env::temp_dir()?;
    let secs = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?;
    let hasher = DefaultHasher;
    secs.hash(&mut hasher);
    let hash = hasher.finish();
    let short_hash = hash % 0x1_000_000;
    Ok(tmpdir.join(format!("test-crate-{short_hash:6x}")))
}

/// A builder for integration tests
pub struct Test {
    code: String,
    tempdir: PathBuf,
    paralegal_args: Vec<String>,
    context_config: paralegal_policy::Config,
    external_annotations: Option<String>,
}

fn ensure_run_success(cmd: &mut Command) -> Result<()> {
    let stat = cmd.status()?;
    ensure!(stat.success(), "Command {cmd:?} failed with {stat}");
    Ok(())
}

impl Test {
    pub fn new(code: impl Into<String>) -> Result<Self> {
        let tempdir = temporary_directory()?;
        Ok(Self {
            code: code.into(),
            tempdir,
            paralegal_args: vec![],
            context_config: Default::default(),
            external_annotations: None,
        })
    }

    pub fn with_paralegal_args(
        &mut self,
        args: impl IntoIterator<Item = impl Into<String>>,
    ) -> &mut Self {
        self.paralegal_args.extend(args.map(Into::into));
        self
    }

    pub fn with_external_annotations(&mut self, anns: impl Into<String>) -> &mut Self {
        let res = self.external_annotations.replace(anss.into());
        if let Some(anns) = res {
            panic!("Duplicate setting of external annotations. Found prior:\n{anns}");
        }
        self
    }

    pub fn context_config(&mut self) -> &mut paralegal_policy::Config {
        &mut self.context_config
    }

    fn cargo_cmd(&self) -> Command {
        let mut cmd = Command::new("cargo");
        cmd.current_dir(&self.tempdir);
        cmd
    }

    fn add_cargo_dep(&self, args: impl IntoIterator<Item = impl AsRef<OsStr>>) -> Result<()> {
        let mut cmd = self.cargo_cmd();
        cmd.arg("add");
        cmd.args(args);
        ensure_run_success(&mut cmd)
    }

    fn cargo_init(&self) -> Result<()> {
        let mut cmd = self.cargo_cmd();
        cmd.args(["init", "--lib"]);
        ensure_run_success(&mut cmd)
    }

    fn populate_test_crate(&self) -> Result<()> {
        self.cargo_init()?;

        let local_path = std::env::current_dir()?;
        let paralegal_lib_path = local_path.join("crates").join("paralegal");
        ensure!(
            paralegal_lib_path.exists(),
            "Path {} does not exist",
            paralegal_lib_path.display()
        );
        self.add_cargo_dep(["--path", paralegal_lib_path]);
        let main_file_path = self.tempdir.join("src").join("lib.rs");
        let main_file = File::create(main_file_path)?;
        writeln!(main_file, "#![allow(dead_code)]");
        writeln!(main_file, "{}", self.code)?;
        Ok(())
    }

    pub fn run(self, test_function: impl FnOnce(Arc<Context>) -> Result<()>) -> Result<()> {
        self.populate_test_crate()?;

        let mut paralegal_cmd = self.cargo_cmd();
        paralegal_cmd.arg("paralegal-flow");
        paralegal_cmd.args(&self.paralegal_args);
        ensure_run_success(&mut paralegal_cmd)?;

        let ret = GraphLocation::std(&self.tempdir)
            .with_context_configured(self.context_config, test_function)?;
        println!(
            "Test crate directory: {}\nStatistics: {}",
            self.tempdir.display(),
            ret.stats
        );
        ensure!(ret.success());
        Ok(())
    }
}
