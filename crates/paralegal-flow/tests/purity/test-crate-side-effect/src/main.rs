#[paralegal::analyze]
fn fs() {
    std::fs::write("test", "Content").unwrap();
}
