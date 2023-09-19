#![feature(register_tool)]
#![register_tool(parable)]

#[parable::label(create)]
fn create() -> Vec<i32> {
    vec![]
}

#[parable::label(read)]
fn read(_: &[i32]) {

}

#[parable::analyze]
fn single_removal() {
    let mut c = create();
    c.push(9);
    read(&c)
}

#[parable::analyze] 
fn double_removal() {
    let mut c = create();
    c.push(9);
    c.truncate(2);
    read(&c)
}

#[parable::label(noinline)]
fn other_push<T>(v: &mut T) {}

#[parable::analyze]
fn labeled_function_not_removed() {
    let mut c = create();
    other_push(&mut c);
    read(&c)
}

#[parable::analyze]
fn source_function_not_removed() {
    let mut c = Vec::new();
    c.push(9);
    read(&c)
}

#[parable::label(create)]
fn create_string() -> String {
    "".to_string()
}

#[parable::analyze]
fn sink_function_not_removed() {
    use std::io::Write;
    let s = create_string();
    std::io::stdout().write(s.as_bytes());

}

#[parable::analyze]
fn no_removal_because_ctrl_out() {
    let s = create();
    if s.is_empty() {
        read(&s)
    }
}

#[parable::analyze]
fn removal_despite_ctrl_in() {
    let mut s = create();
    if s.is_empty() {
        s.push(9);
    }
    read(&s);
}

#[parable::label(create)]
fn create2() -> Vec<i32> {
    vec![]
}

#[parable::label(read)]
fn read2<T>(_: &T) {}

#[parable::analyze]
fn cross_connection_after_removal() {
    let mut s1 = create();
    let mut s2 = create2();
    s1.swap_with_slice(&mut s2);
    read(&s1);
    read2(&s2);
}

fn main() {}