#![feature(register_tool)]
#![register_tool(dfpp)]

#[dfpp::label(hello, return)]
fn source() -> i32 {
    0
}

fn callee(x: i32) -> i32 {
    source()
}

#[dfpp::analyze]
fn with_return() {
    receiver(callee(9));
}

#[dfpp::label(there, arguments = [0])]
fn receiver(x: i32) {}

#[dfpp::analyze] 
fn without_return() {
    callee_2(source());
}

fn callee_2(x: i32) {
    receiver(x);
}

fn main() {}