#![feature(register_tool)]
#![register_tool(dfpp)]


fn source() -> i32 {
    0
}

fn callee(x: i32) -> i32 {
    source()
}

#[dfpp::analyze]
fn caller() {
    receiver(callee(9));
}

fn receiver(x: i32) {}

fn main() {}