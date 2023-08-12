//! The purpose of this application is to 
//! 
//! 1. make rustup download the rustc docs
//! 2. figure out where those docs were stored and move them into the
//!    docs/compiler directory
//! 
//! The reason this is a rust application is because then we can run it easily
//! with `cargo run` and it'll have access to the rustup toolchain and directory
//! information via environment variables. I (Justus) haven't yet been able to
//! query that information easily otherwise.


use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    assert!(Command::new("rustup")
        .args(["component", "add", "rustc-docs"])
        .status()
        .unwrap()
        .success());
    let rustup_folder = std::env::var("RUSTUP_HOME").unwrap();
    let toolchain = std::env::var("RUSTUP_TOOLCHAIN").unwrap();

    let mut src = PathBuf::new();
    for part in [
        rustup_folder.as_str(),
        "toolchains",
        toolchain.as_str(),
        "share",
        "doc",
        "rust",
        "html",
        "rustc",
    ] {
        src.push(part);
    }
    let target = Path::new("../docs/compiler");
    std::fs::rename(src, target).unwrap()
}
