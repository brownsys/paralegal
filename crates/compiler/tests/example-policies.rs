use std::collections::VecDeque;
use std::fs;
use std::path::PathBuf;
use std::{fs::File, io::Write, path::Path, process::Command};

const COMPILER_EXECUTABLE: &str = env!("CARGO_BIN_EXE_paralegal-compiler");
const CARGO_TMPDIR: &str = env!("CARGO_TARGET_TMPDIR");

fn cargo_toml(name: &str) -> String {
    let policy_path = Path::new("../../crates/policy").canonicalize().unwrap();
    include_str!("Cargo.toml")
        .replace("PATH", &policy_path.display().to_string())
        .replace("NAME", name)
}

fn list_files<P: AsRef<Path>>(root: P) -> impl Iterator<Item = std::path::PathBuf> {
    struct FileIter {
        queue: VecDeque<PathBuf>,
    }

    impl Iterator for FileIter {
        type Item = PathBuf;

        fn next(&mut self) -> Option<Self::Item> {
            while let Some(path) = self.queue.pop_front() {
                if path.is_dir() {
                    if let Ok(entries) = fs::read_dir(&path) {
                        for entry in entries.flatten() {
                            self.queue.push_back(entry.path());
                        }
                    }
                } else if path.is_file() {
                    return Some(path);
                }
            }
            None
        }
    }

    let mut queue = VecDeque::new();
    let root = root.as_ref();
    if root.exists() {
        queue.push_back(root.to_path_buf());
    }
    FileIter { queue }
}

#[test]
fn example_policies_compile() {
    let examples_dir = Path::new("../../examples/policies");
    let entries = list_files(examples_dir);
    let output_path = Path::new(CARGO_TMPDIR).join("example-policies");
    println!("Output path is {}", output_path.display());
    if !output_path.exists() {
        std::fs::create_dir(&output_path).expect("Failed to create output directory");
    }
    std::fs::write(
        Path::new(CARGO_TMPDIR).join("rust-toolchain.toml"),
        "[toolchain]
channel = \"1.90\"",
    )
    .unwrap();
    let paths = entries
        .map(|entry| {
            let path = entry.strip_prefix(examples_dir).unwrap();
            let relative_dir_path = path.parent().unwrap().join(path.file_stem().unwrap());
            let name = relative_dir_path.to_string_lossy().replace('/', "-");
            let output_path = output_path.join(&relative_dir_path);
            std::fs::create_dir_all(output_path.join("src")).unwrap();
            let mut cmd = Command::new(COMPILER_EXECUTABLE);
            cmd.arg(examples_dir.join(path))
                .arg("--bin")
                .arg("-o")
                .arg(output_path.join("src").join("main.rs"));
            assert!(
                cmd.status().unwrap().success(),
                "Failed to compile example policy: {}",
                path.display()
            );

            File::create(output_path.join("Cargo.toml"))
                .expect("Failed to create Cargo.toml")
                .write_all(cargo_toml(&name).as_bytes())
                .expect("Failed to write Cargo.toml");
            (relative_dir_path, name)
        })
        .collect::<Vec<_>>();

    File::create(output_path.join("Cargo.toml"))
        .expect("Failed to create Cargo.toml")
        .write_all(
            format!(
                "[workspace]\nmembers = [\n{}\n]\n",
                paths
                    .iter()
                    .map(|(p, _)| format!("\"{}\"", p.display()))
                    .collect::<Vec<_>>()
                    .join(",\n")
            )
            .as_bytes(),
        )
        .expect("Failed to write Cargo.toml");

    let mut build_cmd = Command::new("cargo");
    build_cmd
        .arg("build")
        .env_remove("RUSTUP_TOOLCHAIN")
        .current_dir(&output_path);
    assert!(
        build_cmd.status().unwrap().success(),
        "Failed to build workspace for example policies"
    );

    // Reuses a binary built above rather than building a policy of its own.
    let (_, bin_name) = paths.first().expect("no example policies found");
    skip_pdg_gen_loads_existing_artifact(&output_path, bin_name);

    std::fs::remove_dir_all(output_path).expect("Failed to remove output directory");
}

/// `--skip-pdg-gen` must load the graph named by `dir/paralegal-artifact.json`
/// instead of running the PDG generator in `dir`. An artifact listing no targets
/// is rejected only by the loader, so reaching that error shows the generator
/// was skipped.
fn skip_pdg_gen_loads_existing_artifact(workspace: &Path, bin_name: &str) {
    let bin = workspace.join("target").join("debug").join(bin_name);
    let analyzed = Path::new(CARGO_TMPDIR).join("skip-pdg-gen");
    let artifact = analyzed.join("paralegal-artifact.json");
    std::fs::create_dir_all(&analyzed).unwrap();
    std::fs::write(&artifact, r#"{"targets": []}"#).unwrap();

    let output = Command::new(&bin)
        .arg("--skip-pdg-gen")
        .arg(&analyzed)
        .output()
        .unwrap_or_else(|e| panic!("Failed to run {}: {e}", bin.display()));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success() && stderr.contains("no matching targets found"),
        "expected `--skip-pdg-gen` to load {}, got status {} and stderr:\n{stderr}",
        artifact.display(),
        output.status,
    );

    std::fs::remove_dir_all(analyzed).unwrap();
}
