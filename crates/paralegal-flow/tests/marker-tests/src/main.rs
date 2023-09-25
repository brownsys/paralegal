
#![feature(register_tool)]
#![register_tool(paralegal_flow)]

#[derive(Clone)]
#[repr(transparent)]
#[paralegal_flow::marker(wrapper)]
pub struct Wrapper<T: ?Sized>(T);

fn make_wrapper() -> Result<std::sync::Arc<Wrapper<u32>>, String> {
    unimplemented!()
}

fn consume_any<T>(w: T) {
    unimplemented!()
}

#[paralegal_flow::analyze]
fn use_wrapper() {
    consume_any(make_wrapper())
}


