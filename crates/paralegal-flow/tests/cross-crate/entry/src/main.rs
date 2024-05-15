extern crate dependency;

use dependency::find_me;

#[paralegal::marker(source)]
fn src() -> usize {
    0
}

#[paralegal::marker(not_source)]
fn not_source() -> usize {
    1
}

#[paralegal::marker(target)]
fn target(u: usize) {}

#[paralegal::analyze]
fn main() {
    target(find_me(src(), not_source()))
}
