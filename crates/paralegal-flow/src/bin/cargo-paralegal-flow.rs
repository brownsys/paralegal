extern crate rustc_plugin;
fn main() {
    rustc_plugin::cli_main(paralegal_flow::DfppPlugin);
}
