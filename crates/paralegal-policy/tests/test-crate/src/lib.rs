#![feature(register_tool)]
#![register_tool(paralegal_flow)]

#[paralegal_flow::marker(input)]
pub struct Foo;

#[paralegal_flow::marker{ sink, arguments = [0] }]
#[paralegal_flow::marker{ sink, return }]
fn sink1(_f: Foo) {}

#[paralegal_flow::marker{ src, return }]
fn identity(f: Foo) -> Foo {
    f
}

#[paralegal_flow::marker{ sink, arguments = [0] }]
fn sink2(_f: Foo) {}

#[paralegal_flow::marker{ cond, arguments = [0] }]
fn cond(_f: Foo) -> bool {
    return true;
}

#[paralegal_flow::analyze]
#[paralegal_flow::marker{ ctrl, return }]
#[paralegal_flow::marker{ ctrl, arguments = [2] }]
fn controller(a: Foo, b: Foo, c: bool) -> bool {
    sink1(a);
    sink2(identity(b));
    c
}

#[paralegal_flow::analyze]
fn controller_data_ctrl(a: Foo, b: Foo) {
    if cond(a) {
        sink1(b);
    }
}

#[paralegal_flow::analyze]
fn controller_ctrl(a: bool, b: Foo, c: bool, d: Foo) {
    if a {
        sink1(b);
        if c {
            sink2(d);
        }
    }
}

#[paralegal_flow::analyze]
fn influence(a: Foo, b: Foo) {
    if cond(a) {
        sink1(b);
    }
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
