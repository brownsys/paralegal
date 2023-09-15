#![feature(register_tool)]
#![register_tool(dfpp)]

#[dfpp::marker(input)]
pub struct Foo;

#[dfpp::label{ sink, arguments = [0] }]
fn sink1(_f: Foo) {}

#[dfpp::label{ sink, arguments = [0] }]
fn sink2(_f: Foo) {}

#[dfpp::analyze]
fn controller(a: Foo, b: Foo) {
    sink1(a);
    sink2(b);
}

#[dfpp::marker(start, return)]
fn create() -> u32 {
    9
}

#[dfpp::marker(bless, arguments = [0])]
fn id<T>(t: T) -> T {
    t
}

#[dfpp::analyze]
fn happens_before_pass() -> u32 {
    id(create())
}

#[dfpp::analyze]
fn happens_before_fail() -> u32 {
    let val = create();
    id(val) + val
}