#![feature(register_tool)]
#![register_tool(paralegal_flow)]

use std::vec::Vec;

#[paralegal_flow::analyze]
fn main() {
    let mut v = Vec::new();
    v.push(0);
	v.push(1);
}
