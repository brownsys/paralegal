#![feature(string_remove_matches)]

use std::env;
use std::path::PathBuf;
use std::process::Command;

/// The "SYSROOT" path for the toolchain we're compiling against.
/// ($RUSTUP_HOME/toolchains/$RUSTUP_TOOLCHAIN)
fn rustup_toolchain_path() -> PathBuf {
    if let Ok(sysroot) = Command::new("rustc").arg("--print").arg("sysroot").output() {
        return PathBuf::from(
            String::from_utf8(sysroot.stdout)
                .unwrap()
                .trim()
                .to_string(),
        );
    }

    let rustup_home = env::var("RUSTUP_HOME").unwrap();
    let rustup_tc = env::var("RUSTUP_TOOLCHAIN").unwrap();
    [&rustup_home, "toolchains", &rustup_tc]
        .into_iter()
        .collect()
}

fn main() {
    let toolchain_path = rustup_toolchain_path();
    println!("cargo:rustc-env=SYSROOT_PATH={}", toolchain_path.display());
}
