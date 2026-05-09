use paralegal_utils::linux_workaround_for_llvm_lib;

fn main() {
    linux_workaround_for_llvm_lib();

    let autocfg = autocfg::AutoCfg::new().unwrap();
    autocfg.emit_rustc_version(1, 75);
}
