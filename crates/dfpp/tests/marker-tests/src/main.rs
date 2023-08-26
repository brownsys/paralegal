
#![feature(register_tool)]
#![register_tool(dfpp)]

#[derive(Clone)]
#[repr(transparent)]
#[dfpp::marker(wrapper)]
pub struct Wrapper<T: ?Sized>(T);

fn make_wrapper() -> Result<std::sync::Arc<Wrapper<u32>>, String> {
    unimplemented!()
}

fn consume_any<T>(w: T) {
    unimplemented!()
}

#[dfpp::analyze]
fn use_wrapper() {
    consume_any(make_wrapper())
}


