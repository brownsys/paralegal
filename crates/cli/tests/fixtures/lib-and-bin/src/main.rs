use cli_test_lib_and_bin::lib_entrypoint;

#[paralegal::marker(bin_marker)]
fn marked_in_bin() {}

#[paralegal::analyze]
fn bin_entrypoint() {
    marked_in_bin();
    // Pull the lib into the bin's dep graph so cargo actually compiles
    // it — otherwise `cargo build` of the bin alone wouldn't trigger
    // analysis of the lib.
    lib_entrypoint();
}

fn main() {
    bin_entrypoint();
}
