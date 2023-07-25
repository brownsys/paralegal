#![feature(register_tool)]
#![register_tool(dfpp)]

use std::vec::Vec;

#[dfpp::analyze]
fn main() {
    let mut v = Vec::new();
    v.push(0);
	v.push(1);
}
