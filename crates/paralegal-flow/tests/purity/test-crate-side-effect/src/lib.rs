#[paralegal::analyze]
fn fs() {
    std::fs::write("test", "Content").unwrap();
}

#[paralegal::analyze]
fn path_eq() {
    std::path::Path::new("test") == std::path::Path::new("test");
}

#[paralegal::analyze]
fn os_str_from_bytes() {
    use std::os::unix::prelude::OsStrExt;
    std::ffi::OsStr::from_bytes(b"test");
}
