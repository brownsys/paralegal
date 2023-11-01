#[paralegal::marker(create)]
fn create() -> Vec<i32> {
    vec![]
}

#[paralegal::marker(read)]
fn read(_: &[i32]) {}

#[paralegal::analyze]
fn single_removal() {
    let mut c = create();
    c.push(9);
    read(&c)
}

#[paralegal::analyze]
fn double_removal() {
    let mut c = create();
    c.push(9);
    c.truncate(2);
    read(&c)
}

#[paralegal::marker(noinline)]
fn other_push<T>(v: &mut T) {}

#[paralegal::analyze]
fn labeled_function_not_removed() {
    let mut c = create();
    other_push(&mut c);
    read(&c)
}

#[paralegal::analyze]
fn source_function_not_removed() {
    let mut c = Vec::new();
    c.push(9);
    read(&c)
}

#[paralegal::marker(create)]
fn create_string() -> String {
    "".to_string()
}

#[paralegal::analyze]
fn sink_function_not_removed() {
    use std::io::Write;
    let s = create_string();
    std::io::stdout().write(s.as_bytes());
}

#[paralegal::analyze]
fn no_removal_because_ctrl_out() {
    let s = create();
    if s.is_empty() {
        read(&s)
    }
}

#[paralegal::analyze]
fn removal_despite_ctrl_in() {
    let mut s = create();
    if s.is_empty() {
        s.push(9);
    }
    read(&s);
}

#[paralegal::marker(create)]
fn create2() -> Vec<i32> {
    vec![]
}

#[paralegal::marker(read)]
fn read2<T>(_: &T) {}

#[paralegal::analyze]
fn cross_connection_after_removal() {
    let mut s1 = create();
    let mut s2 = create2();
    s1.swap_with_slice(&mut s2);
    read(&s1);
    read2(&s2);
}

fn main() {}
