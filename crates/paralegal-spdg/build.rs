use anyhow::Context;
use anyhow::Result;
use std::collections::hash_map::DefaultHasher;
use std::env;
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::time::SystemTime;

fn rustup_toolchain_path() -> PathBuf {
    let rustup_home = env::var("RUSTUP_HOME").unwrap();
    let rustup_tc = env::var("RUSTUP_TOOLCHAIN").unwrap();
    [&rustup_home, "toolchains", &rustup_tc]
        .into_iter()
        .collect()
}

fn get_rustup_lib_path() -> PathBuf {
    let mut rustup_lib = rustup_toolchain_path();
    rustup_lib.push("lib");
    rustup_lib
}

/// Helper for calculating a hash of all (modification dates of) Rust files in this crate.
fn visit_dirs(dir: &Path, hasher: &mut DefaultHasher) -> Result<()> {
    if !dir.is_dir() {
        return Ok(());
    }
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            visit_dirs(&path, hasher)?;
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            let metadata = entry.metadata()?;
            let modified = metadata.modified()?;

            let duration = modified.duration_since(SystemTime::UNIX_EPOCH)?;
            duration.as_secs().hash(hasher);
            // Tell Cargo to rerun if this source file changes
            println!("cargo:rerun-if-changed={}", path.display());
        }
    }
    Ok(())
}

/// Calculate a hash of all (modification dates of) Rust files in this crate.
fn calculate_source_hash() -> u64 {
    let mut hasher = DefaultHasher::new();

    // Start from the src directory
    visit_dirs(Path::new("src"), &mut hasher)
        .with_context(|| "Calculating source hash")
        .unwrap();

    hasher.finish()
}

fn main() {
    let magic = calculate_source_hash();

    // Emit the hash as an environment variable
    println!("cargo:rustc-env=SER_MAGIC={:0}", magic);

    // Original linux-specific code
    if cfg!(target_os = "linux") {
        let rustup_lib = get_rustup_lib_path();
        println!("cargo:rustc-link-search=native={}", rustup_lib.display());
    }
}
