#![feature(register_tool)]
#![register_tool(parable)]

#[parable::label(hello, return)]
fn source() -> i32 {
    0
}

fn callee(x: i32) -> i32 {
    source()
}

#[parable::analyze]
fn with_return(x: i32) {
    receiver(callee(x));
}

#[parable::label(there, arguments = [0])]
fn receiver(x: i32) {}

#[parable::analyze]
fn without_return() {
    callee_2(source());
}

fn callee_2(x: i32) {
    receiver(x);
}

#[parable::analyze]
fn on_mut_var() {
    let mut x = 4;
    modify_it(&mut x);
    receiver(x)
}

fn modify_it(x: &mut i32) {
    *x = source();
}

fn dont_modify_it(x: &mut i32) -> i32 {
    source()
}

#[parable::analyze]
fn on_mut_var_no_modify() {
    let mut x = 4;
    dont_modify_it(&mut x);
    receiver(x)
}

#[derive(Clone)]
struct S {
    usize_field: usize,
    string_field: String,
}

#[parable::label(noinline, return)]
fn read_usize(u: usize) {}

#[parable::label(noinline ,return)]
fn read_string(s: String) {}

fn modify_a_field(s: &mut S) {
    s.usize_field = produce_usize();
}

#[parable::label(noinline ,return)]
fn produce_usize() -> usize {
    0
}

#[parable::label(noinline ,return)]
fn produce_string() -> String {
    "".to_string()
}

#[parable::analyze]
fn field_sensitivity() {
    let distraction = 4;
    let mut s = S {
        usize_field: 0,
        string_field: produce_string(),
    };
    modify_a_field(&mut s);
    read_usize(s.usize_field);
    read_string(s.string_field);
    read_usize(distraction);
}

fn main() {}

#[parable::label(otherwise_unused)]
fn unused() {}

#[parable::analyze]
fn field_sensitivity_across_clone() {
    let distraction = 4;
    let mut s = S {
        usize_field: produce_usize(),
        string_field: produce_string(),
    };
    let s = (&s).clone();
    read_usize(s.usize_field);
    read_string(s.string_field);
    read_usize(distraction);
}
