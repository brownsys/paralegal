use std::{
    collections::hash_map::DefaultHasher,
    env,
    ffi::{OsStr, OsString},
    fs::{self, File},
    hash::{Hash, Hasher},
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
    time::SystemTime,
};

use anyhow::anyhow;
pub use anyhow::{ensure, Result};

use paralegal_policy::{Context, GraphLocation};

lazy_static::lazy_static! {
    static ref TOOL_BUILT: PathBuf = {
        let dir = std::env::current_dir().unwrap();
        let flow_dir = dir.parent().unwrap().join("paralegal-flow");
        assert!(flow_dir.exists(), "{}", flow_dir.display());
        let mut build_cmd = Command::new("cargo");
        build_cmd.args(["build", "--release"]);
        build_cmd.current_dir(flow_dir);
        let stat = build_cmd.status().unwrap();
        assert!(stat.success());
        let tool_path = dir.parent().unwrap().parent().unwrap().join("target").join("release").join("cargo-paralegal-flow");
        assert!(tool_path.exists(), "{}", tool_path.display());
        tool_path
    };
}

fn temporary_directory() -> Result<PathBuf> {
    let tmpdir = env::temp_dir();
    let secs = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?;
    let mut hasher = DefaultHasher::new();
    secs.hash(&mut hasher);
    let hash = hasher.finish();
    let short_hash = hash % 0x1_000_000;
    let path = tmpdir.join(format!("test-crate-{short_hash:06x}"));
    fs::create_dir(&path)?;
    Ok(path)
}

/// A builder for integration tests
pub struct Test {
    code: String,
    tempdir: PathBuf,
    paralegal_args: Vec<String>,
    context_config: paralegal_policy::Config,
    external_annotations: Option<String>,
    deps: Vec<Vec<OsString>>,
    tool_path: &'static Path,
    external_ann_file_name: PathBuf,
    cleanup: bool,
}

fn ensure_run_success(cmd: &mut Command) -> Result<()> {
    let stat = cmd.status()?;
    ensure!(stat.success(), "Command {cmd:?} failed with {stat}");
    Ok(())
}

impl Test {
    #[allow(dead_code)]
    pub fn new(code: impl Into<String>) -> Result<Self> {
        let tempdir = temporary_directory()?;
        Ok(Self {
            code: code.into(),
            external_ann_file_name: tempdir.join("external_annotations.toml"),
            tempdir,
            paralegal_args: vec![],
            context_config: Default::default(),
            external_annotations: None,
            tool_path: &*TOOL_BUILT,
            deps: Default::default(),
            cleanup: true,
        })
    }

    #[allow(dead_code)]
    pub fn with_cleanup(&mut self, cleanup: bool) -> &mut Self {
        self.cleanup = cleanup;
        self
    }

    #[allow(dead_code)]
    pub fn with_paralegal_args(
        &mut self,
        args: impl IntoIterator<Item = impl Into<String>>,
    ) -> &mut Self {
        self.paralegal_args.extend(args.into_iter().map(Into::into));
        self
    }

    #[allow(dead_code)]
    pub fn with_external_annotations(&mut self, anns: impl Into<String>) -> &mut Self {
        let res = self.external_annotations.replace(anns.into());
        if let Some(anns) = res {
            panic!("Duplicate setting of external annotations. Found prior:\n{anns}");
        }
        self
    }

    /// Add additional dependencies. The argument to this function are command
    /// line arguments as would be given to `cargo add`. You may call this
    /// function multiple times fo add more dependencies.
    #[allow(dead_code)]
    pub fn with_dep(&mut self, it: impl IntoIterator<Item = impl Into<OsString>>) -> &mut Self {
        self.deps.push(it.into_iter().map(Into::into).collect());
        self
    }

    #[allow(dead_code)]
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
        use std::io::Write;
        self.cargo_init()?;

        let local_path = std::env::current_dir()?;
        let paralegal_lib_path = local_path
            .parent()
            .ok_or(anyhow!("local path has no parent"))?
            .join("paralegal");
        ensure!(
            paralegal_lib_path.exists(),
            "Path {} does not exist",
            paralegal_lib_path.display()
        );
        self.add_cargo_dep([OsStr::new("--path"), paralegal_lib_path.as_os_str()])?;
        for dep in &self.deps {
            self.add_cargo_dep(dep)?;
        }
        if let Some(external_anns) = self.external_annotations.as_ref() {
            let mut f = File::create(&self.external_ann_file_name)?;
            writeln!(f, "{external_anns}")?;
        }

        let main_file_path = self.tempdir.join("src").join("lib.rs");
        let mut main_file = File::create(main_file_path)?;
        writeln!(main_file, "#![allow(dead_code)]")?;
        writeln!(main_file, "{}", self.code)?;
        Ok(())
    }

    #[allow(dead_code)]
    pub fn run(self, test_function: impl FnOnce(Arc<Context>) -> Result<()>) -> Result<()> {
        self.populate_test_crate()?;

        let mut paralegal_cmd = Command::new(self.tool_path);
        paralegal_cmd.arg("paralegal-flow");
        if self.external_annotations.is_some() {
            paralegal_cmd.args([
                OsStr::new("--external-annotations"),
                self.external_ann_file_name.as_os_str(),
            ]);
        }
        paralegal_cmd.args(&self.paralegal_args);
        paralegal_cmd.current_dir(&self.tempdir);
        ensure_run_success(&mut paralegal_cmd)?;

        let ret = GraphLocation::std(&self.tempdir)
            .with_context_configured(self.context_config, test_function)?;
        println!(
            "Test crate directory: {}\nStatistics: {}",
            self.tempdir.display(),
            ret.stats
        );
        ensure!(ret.success);
        if self.cleanup {
            fs::remove_dir_all(self.tempdir)?;
        }
        Ok(())
    }
}
