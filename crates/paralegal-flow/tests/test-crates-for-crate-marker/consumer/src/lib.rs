#[paralegal::analyze]
fn crate_marker() {
    producer::target();
}

#[paralegal::analyze]
fn serde_json() {
    serde_json::to_string(&34_i32).unwrap();
}
