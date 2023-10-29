#[paralegal::marker(input)]
pub struct Foo;

#[paralegal::marker{ sink, arguments = [0] }]
fn sink1(_f: Foo) {}

#[paralegal::marker{ src, return }]
fn identity(f: Foo) -> Foo {
    f
}

#[paralegal::marker{ sink, arguments = [0] }]
fn sink2(_f: Foo) {}

#[paralegal::marker{ cond, arguments = [0] }]
fn cond(_f: Foo) -> bool {
    return true;
}

#[paralegal::analyze]
#[paralegal::marker{ ctrl, return }]
#[paralegal::marker{ ctrl, arguments = [2] }]
fn controller(a: Foo, b: Foo, c: bool) -> bool {
    sink1(a);
    sink2(identity(b));
    c
}

#[paralegal::analyze]
fn controller_data_ctrl(a: Foo, b: Foo) {
    if cond(a) {
        sink1(b);
    }
}

#[paralegal::analyze]
fn controller_ctrl(a: bool, b: Foo, c: bool, d: Foo) {
    if a {
        sink1(b);
        if c {
            sink2(d);
        }
    }
}

#[paralegal::marker(start, return)]
fn create() -> u32 {
    9
}

#[paralegal::marker(bless, arguments = [0])]
fn id<T>(t: T) -> T {
    t
}

#[paralegal::analyze]
fn happens_before_pass() -> u32 {
    id(create())
}

#[paralegal::analyze]
fn happens_before_fail() -> u32 {
    let val = create();
    id(val) + val
}
