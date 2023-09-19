#![feature(register_tool)]
#![register_tool(parable)]

#[parable::marker(input)]
pub struct Foo;

#[parable::label{ sink, arguments = [0] }]
fn sink1(_f: Foo) {}

#[parable::label{ sink, arguments = [0] }]
fn sink2(_f: Foo) {}

#[parable::analyze]
fn controller(a: Foo, b: Foo) {
    sink1(a);
    sink2(b);
}

#[parable::marker(start, return)]
fn create() -> u32 {
    9
}

#[parable::marker(bless, arguments = [0])]
fn id<T>(t: T) -> T {
    t
}

#[parable::analyze]
fn happens_before_pass() -> u32 {
    id(create())
}

#[parable::analyze]
fn happens_before_fail() -> u32 {
    let val = create();
    id(val) + val
}