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
