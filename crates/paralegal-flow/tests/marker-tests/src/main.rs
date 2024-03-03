#[derive(Clone)]
//#[repr(transparent)]
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

trait Test {
    #[paralegal::marker(find_me)]
    fn method(self);
}

impl Test for () {
    fn method(self) {}
}

#[paralegal::analyze]
fn trait_method_marker() {
    ().method()
}

#[paralegal::analyze]
fn typed_input(w: Wrapper<u32>) {
    consume_any(w)
}
