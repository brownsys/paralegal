extern crate rustc_plugin;
fn main() {
    rustc_plugin::cli_main(dfpp::DfppPlugin);
}
