extern crate dependency;

use dependency::*;

#[paralegal::marker(source, return)]
fn src() -> usize {
    0
}

#[paralegal::marker(not_source)]
fn not_src() -> usize {
    1
}

#[paralegal::marker(target, arguments = [0])]
fn target(u: usize) {}

#[paralegal::analyze]
fn basic() {
    target(find_me(src(), not_src()))
}

#[paralegal::analyze]
fn basic_marker() {
    target(source());
}

#[paralegal::analyze]
fn assigns_marker() {
    target(assign_marker(src()));
}

#[paralegal::analyze]
fn basic_generic() {
    target(find_me_generic(src(), not_src()))
}

#[paralegal::analyze]
fn assigns_marker_generic() {
    target(assign_marker_generic(src()));
}

#[paralegal::analyze]
fn backward_simple() {
    hof(|inp| target(inp));
}

#[paralegal::analyze]
fn donation() {
    struct D;
    impl Donator for D {
        fn donate(&self) -> String {
            src().to_string()
        }
    }

    exercise_donate(&D);
}

#[paralegal::analyze]
fn reception() {
    struct R;

    impl Receiver for R {
        fn receive(&self, value: String) {
            target(value.len())
        }
    }

    exercise_receive(&R);
}

fn main() {}
