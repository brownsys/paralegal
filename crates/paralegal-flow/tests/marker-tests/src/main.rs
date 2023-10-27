
#[derive(Clone)]
#[repr(transparent)]
#[paralegal::marker(wrapper)]
pub struct Wrapper<T: ?Sized>(T);

fn make_wrapper() -> Result<std::sync::Arc<Wrapper<u32>>, String> {
    unimplemented!()
}

fn consume_any<T>(w: T) {
    unimplemented!()
}

#[paralegal::analyze]
fn use_wrapper() {
    consume_any(make_wrapper())
}
