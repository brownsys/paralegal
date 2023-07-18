use std::path::PathBuf;
use std::process::Command;
extern crate chrono;
use std::env;

/// Taken from Kani
/// (<https://github.com/model-checking/kani/blob/3d8ceddb0672e1dda6c186830f411c979bc132e2/kani-compiler/build.rs>)
/// this code links the rustc libraries directly with the compiled binaries.
pub fn link_rustc_lib() {
    // Add rustup to the rpath in order to properly link with the correct rustc version.
    let rustup_home = env::var("RUSTUP_HOME").unwrap();
    let rustup_tc = env::var("RUSTUP_TOOLCHAIN").unwrap();
    let rustup_lib = [&rustup_home, "toolchains", &rustup_tc, "lib"]
        .into_iter()
        .collect::<PathBuf>();
    println!(
        "cargo:rustc-link-arg-bin=dfpp=-Wl,-rpath,{}",
        rustup_lib.display()
    );
    println!(
        "cargo:rustc-link-arg-bin=cargo-dfpp=-Wl,-rpath,{}",
        rustup_lib.display()
    );

    // While we hard-code the above for development purposes, for a release/install we look
    // in a relative location for a symlink to the local rust toolchain
    let origin = if cfg!(target_os = "macos") {
        "@loader_path"
    } else {
        "$ORIGIN"
    };
    println!("cargo:rustc-link-arg-bin=dfpp=-Wl,-rpath,{origin}/../toolchain/lib");
    println!("cargo:rustc-link-arg-bin=cargo-dfpp=-Wl,-rpath,{origin}/../toolchain/lib");
}

fn main() {
    link_rustc_lib();
    println!(
        "cargo:rustc-env=COMMIT_HASH={}",
        Command::new("git")
            .args(&["log", "-n", "1", "--pretty=format:\"%H\""])
            .output()
            .ok()
            .and_then(|o| String::from_utf8(o.stdout).ok())
            .unwrap_or("unknown".to_owned())
    );
    println!(
        "cargo:rustc-env=BUILD_TIME={}",
        chrono::Local::now().format("%a %b %e %T %Y")
    )
}
