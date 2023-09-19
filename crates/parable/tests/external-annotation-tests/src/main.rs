#![feature(register_tool)]
#![register_tool(parable)]

use std::vec::Vec;

#[parable::analyze]
fn main() {
    let mut v = Vec::new();
    v.push(0);
	v.push(1);
}
