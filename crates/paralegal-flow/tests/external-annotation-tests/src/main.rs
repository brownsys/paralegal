use std::vec::Vec;

#[paralegal::analyze]
fn main() {
    let mut v = Vec::new();
    v.push(0);
    v.push(1);
}
