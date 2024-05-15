extern crate dependency;

use dependency::find_me;

#[paralegal::marker(source)]
fn src() -> usize {
    0
}

#[paralegal::marker(not_source)]
fn not_src() -> usize {
    1
}

#[paralegal::marker(target)]
fn target(u: usize) {}

#[paralegal::analyze]
fn basic() {
    target(find_me(src(), not_src()))
}

fn main() {}
