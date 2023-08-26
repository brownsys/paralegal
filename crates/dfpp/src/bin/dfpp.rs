extern crate rustc_plugin;

fn main() {
    rustc_plugin::driver_main(dfpp::DfppPlugin);
}
