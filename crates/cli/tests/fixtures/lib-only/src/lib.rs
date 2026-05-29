#[paralegal::marker(lib_marker)]
pub fn marked_in_lib() {}

#[paralegal::analyze]
pub fn lib_entrypoint() {
    marked_in_lib();
}
