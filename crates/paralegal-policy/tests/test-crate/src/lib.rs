#![feature(register_tool)]
#![register_tool(paralegal_flow)]

#[paralegal_flow::marker(input)]
pub struct Foo;

#[paralegal_flow::label{ sink, arguments = [0] }]
fn sink1(_f: Foo) {}

#[paralegal_flow::label{ sink, arguments = [0] }]
fn sink2(_f: Foo) {}

#[paralegal_flow::analyze]
fn controller(a: Foo, b: Foo) {
    sink1(a);
    sink2(b);
}

#[paralegal_flow::marker(start, return)]
fn create() -> u32 {
    9
}

#[paralegal_flow::marker(bless, arguments = [0])]
fn id<T>(t: T) -> T {
    t
}

#[paralegal_flow::analyze]
fn happens_before_pass() -> u32 {
    id(create())
}

#[paralegal_flow::analyze]
fn happens_before_fail() -> u32 {
    let val = create();
    id(val) + val
}