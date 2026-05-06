use anyhow::Context;
use anyhow::Result;
use paralegal_non_rustc_utils::linux_workaround_for_llvm_lib;
use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::Path;
use std::time::SystemTime;


fn hash_via_content(path: &Path, hasher: &mut DefaultHasher) -> std::io::Result<()> {
    use std::io::Read;
    let mut file = std::fs::File::open(path)?;
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;
    buffer.hash(hasher);
    Ok(())
}

/// Helper for calculating a hash of all Rust files in this crate.
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
            hash_via_content(&path, hasher)?;
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

    linux_workaround_for_llvm_lib();
}
