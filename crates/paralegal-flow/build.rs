#![feature(string_remove_matches)]

use std::path::PathBuf;
use std::process::Command;
extern crate chrono;
use std::env;

const COMPILER_DEPENDENT_BINARIES: &[&str] = &["paralegal-flow", "cargo-paralegal-flow"];

fn add_link_arg_for_compiler_binaries(s: impl std::fmt::Display) {
    for bin in COMPILER_DEPENDENT_BINARIES {
        println!("cargo:rustc-link-arg-bin={bin}={s}");
    }
}

fn add_link_search_path_for_compiler_binaries(s: impl std::fmt::Display) {
    add_link_arg_for_compiler_binaries(format!("-Wl,-rpath,{s}"))
}

/// The "SYSROOT" path for the toolchain we're compiling against.
/// ($RUSTUP_HOME/toolchains/$RUSTUP_TOOLCHAIN)
fn rustup_toolchain_path() -> PathBuf {
    let rustup_home = env::var("RUSTUP_HOME").unwrap();
    let rustup_tc = env::var("RUSTUP_TOOLCHAIN").unwrap();
    [&rustup_home, "toolchains", &rustup_tc]
        .into_iter()
        .collect()
}

/// Taken from Kani
/// (<https://github.com/model-checking/kani/blob/3d8ceddb0672e1dda6c186830f411c979bc132e2/kani-compiler/build.rs>)
/// this code links the rustc libraries directly with the compiled binaries.
pub fn link_rustc_lib() {
    // Add rustup to the rpath in order to properly link with the correct rustc version.
    let mut rustup_lib = rustup_toolchain_path();
    rustup_lib.push("lib");
    add_link_search_path_for_compiler_binaries(rustup_lib.display());

    // While we hard-code the above for development purposes, for a release/install we look
    // in a relative location for a symlink to the local rust toolchain
    let origin = if cfg!(target_os = "macos") {
        "@loader_path"
    } else {
        "$ORIGIN"
    };
    add_link_search_path_for_compiler_binaries(format!("{origin}/../toolchain/lib"));
    if cfg!(target_os = "linux") {
        println!("cargo:rustc-link-search=native={}", rustup_lib.display());
    }
}

fn main() {
    link_rustc_lib();
    println!(
        "cargo:rustc-env=COMMIT_HASH={}",
        Command::new("git")
            .args(["log", "-n", "1", "--pretty=format:\"%H\""])
            .output()
            .ok()
            .and_then(|o| String::from_utf8(o.stdout).ok())
            .unwrap_or("unknown".to_owned())
    );
    println!(
        "cargo:rustc-env=BUILD_TIME={}",
        chrono::Local::now().format("%a %b %e %T %Y")
    );

    let toolchain_path = rustup_toolchain_path();
    println!("cargo:rustc-env=SYSROOT_PATH={}", toolchain_path.display());

    let rustc_path = std::env::var("RUSTC").unwrap();
    let rustc_version = std::process::Command::new(rustc_path)
        .arg("--version")
        .output()
        .unwrap();
    let mut version_str = String::from_utf8(rustc_version.stdout).unwrap();
    version_str.remove_matches('\n');
    println!("cargo:rustc-env=RUSTC_VERSION={}", version_str,);
}
