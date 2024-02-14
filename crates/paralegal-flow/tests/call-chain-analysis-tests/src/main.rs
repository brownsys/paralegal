#[paralegal::marker(hello, return)]
fn source() -> i32 {
    0
}

fn callee(x: i32) -> i32 {
    source()
}

#[paralegal::analyze]
fn with_return(x: i32) {
    receiver(callee(x));
}

#[paralegal::marker(there, arguments = [0])]
fn receiver(x: i32) {}

#[paralegal::analyze]
fn without_return() {
    callee_2(source());
}

fn callee_2(x: i32) {
    receiver(x);
}

#[paralegal::analyze]
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

#[paralegal::analyze]
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

#[paralegal::marker(noinline, return)]
fn read_usize(u: usize) {}

#[paralegal::marker(noinline, return)]
fn read_string(s: String) {}

fn modify_a_field(s: &mut S) {
    s.usize_field = produce_usize();
}

#[paralegal::marker(noinline, return)]
fn produce_usize() -> usize {
    0
}

#[paralegal::marker(noinline, return)]
fn produce_string() -> String {
    "".to_string()
}

#[paralegal::analyze]
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

#[paralegal::marker(otherwise_unused)]
fn unused() {}

#[paralegal::analyze]
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

#[paralegal::marker(noinline)]
fn input() -> usize {
    0
}

fn generic_id_fun<T>(t: T) -> T {
    t
}

fn id_fun<T, G>(t: (T, G)) -> (T, G) {
    t
}

#[paralegal::marker(noinline)]
fn target<T>(t: T) {}

#[paralegal::marker(noinline)]
fn another_target<T>(t: T) {}

#[paralegal::analyze]
fn no_overtaint_over_fn_call() {
    let p = input();
    let q = source();
    let t = id_fun((p, q));
    target(t.0);
    another_target(t.1);
}

#[paralegal::analyze]
fn no_overtaint_over_generic_fn_call() {
    let p = input();
    let q = source();
    let t = generic_id_fun((p, q));
    target(t.0);
    another_target(t.1);
}

#[paralegal::analyze]
fn no_overtaint_over_nested_fn_call() {
    let p = input();
    let q = source();
    forwarder((p, q));
}

fn forwarder(t: (usize, i32)) {
    acceptor(t)
}

fn acceptor(t: (usize, i32)) {
    target(t.0);
    another_target(t.1);
}
