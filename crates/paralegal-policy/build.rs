use std::env;
use std::path::PathBuf;
use std::process::Command;

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

fn get_rustup_lib_path() -> PathBuf {
    let mut rustup_lib = rustup_toolchain_path();
    rustup_lib.push("lib");
    rustup_lib
}

fn main() {
    if cfg!(target_os = "linux") {
        let rustup_lib = get_rustup_lib_path();
        println!("cargo:rustc-link-search=native={}", rustup_lib.display());
    }

    let autocfg = autocfg::AutoCfg::new().unwrap();

    autocfg.emit_rustc_version(1, 75);
}
