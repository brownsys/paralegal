use std::collections::VecDeque;
use std::fs;
use std::path::PathBuf;
use std::{fs::File, io::Write, path::Path, process::Command};

const COMPILER_EXECUTABLE: &str = env!("CARGO_BIN_EXE_paralegal-compiler");
const CARGO_TMPDIR: &str = env!("CARGO_TARGET_TMPDIR");

fn cargo_toml(name: &str) -> String {
    let policy_path = Path::new("../../crates/paralegal-policy")
        .canonicalize()
        .unwrap();
    format!(
        "
[package]
name = \"{name}\"
version = \"0.1.0\"
edition = \"2021\"

[dependencies]
anyhow = \"1\"
paralegal-policy = {{ path = \"{}\" }}
clap = {{ version = \"4\", features = [\"derive\"] }}
",
        policy_path.display()
    )
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
    let paths = entries
        .map(|entry| {
            let path = entry.strip_prefix(examples_dir).unwrap();
            let relative_dir_path = path.parent().unwrap().join(path.file_stem().unwrap());
            let name = relative_dir_path.to_string_lossy().replace('/', "-");
            let output_path = output_path.join(&relative_dir_path);
            std::fs::create_dir_all(output_path.join("src")).unwrap();
            let mut cmd = Command::new(COMPILER_EXECUTABLE);
            cmd.arg(&examples_dir.join(path))
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
            relative_dir_path
        })
        .collect::<Vec<_>>();

    File::create(output_path.join("Cargo.toml"))
        .expect("Failed to create Cargo.toml")
        .write_all(
            format!(
                "[workspace]\nmembers = [\n{}\n]\n",
                paths
                    .iter()
                    .map(|p| format!("\"{}\"", p.display()))
                    .collect::<Vec<_>>()
                    .join(",\n")
            )
            .as_bytes(),
        )
        .expect("Failed to write Cargo.toml");

    let mut build_cmd = Command::new("cargo");
    build_cmd.arg("build").current_dir(&output_path);
    assert!(
        build_cmd.status().unwrap().success(),
        "Failed to build workspace for example policies"
    );

    std::fs::remove_dir_all(output_path).expect("Failed to remove output directory");
}
