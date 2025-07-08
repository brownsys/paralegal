use std::{env, path::Path, process::Command};

fn main() {
    let p = Path::new("policy.txt");
    println!("cargo:rerun-if-changed={}", p.display());
    let out_dir = env::var_os("OUT_DIR").unwrap();
    let mut out_file = Path::new(&out_dir).join(p);
    out_file.set_extension("rs");
    let status = Command::new("cargo")
        .args(["run", "-p", "paralegal-compiler", "--"])
        .arg(p)
        .arg("-o")
        .arg(out_file)
        .arg("--standalone")
        .current_dir("../..")
        .status()
        .unwrap();
    assert!(status.success());
}
