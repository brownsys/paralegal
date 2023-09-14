#![feature(register_tool)]
#![register_tool(dfpp)]

#[dfpp::marker(source)]
fn input() -> i32 {
    0
}

#[dfpp::marker(sink)]
fn sink(i: i32) -> Option<()> {
    None
}

fn call_arg<R, F: FnOnce() -> R>(i: i32, f: F) -> R {
    f()
}

fn call<R, F: FnOnce() -> R>(f: F) -> R {
    f()
}

fn call_1<R, F: FnOnce(i32) -> R>(f:F) -> R {
    f(1)
}

#[dfpp::analyze]
fn simple() {
    let source = input();
    std::iter::from_fn(|| {
        sink(source)
    });
}

#[dfpp::analyze]
fn local() {
    let source = input();
    call(|| {
        sink(source)
    });
}

#[dfpp::analyze]
fn closure_arg() {
    let source = input();
    call_1(|_| 
        sink(source)
    );
}

#[dfpp::analyze]
fn caller_arg() {
    let source = input();
    call_arg(0, || 
        sink(source)
    );
}

#[dfpp::analyze]
fn return_connect() {
    let source = call(|| {
        input()
    });
    sink(source);
}

fn main() {}