use std::fs::{rename, File};
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
    assert!(src.exists());
    assert!(target.parent().unwrap().exists());
    //std::fs::rename(src, ).unwrap(target)
}
