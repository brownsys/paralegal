#![feature(register_tool)]
#![register_tool(dfpp)]

#[dfpp::analyze]
fn main() {
    let mut v = Vec::new();
    v.push(0);
	v.push(1);
}
