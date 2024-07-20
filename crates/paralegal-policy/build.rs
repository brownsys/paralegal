fn main() {
    if cfg!(target_os = "linux") {
        println!("cargo:rustc-link-search=native={}", rustup_lib.display());
    }
}
