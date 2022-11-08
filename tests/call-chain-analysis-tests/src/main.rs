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
fn with_return(x: i32) {
    receiver(callee(x));
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

#[dfpp::analyze]
fn on_mut_var() {
    let mut x = 4;
    modify_it(&mut x);
    receiver(x)
}

fn modify_it(x: &mut i32) {
    *x = source();
}

fn dont_modify_it(x: &mut i32) -> i32 {
    source()
}

#[dfpp::analyze]
fn on_mut_var_no_modify() {
    let mut x = 4;
    dont_modify_it(&mut x);
    receiver(x)
}


fn main() {


}