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
    #[paralegal::marker(find_me, arguments = [0])]
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
fn wrapping_typed_input(w: Wrapper<u32>) {
    consume_any(w)
}

#[paralegal::marker(marked)]
struct Marked {
    f1: usize,
    f2: bool,
}

#[paralegal::analyze]
fn typed_input(w: Marked) {
    consume_any(w)
}

#[paralegal::marker(marked)]
struct MarkedZST;

#[paralegal::analyze]
fn typed_input_zst(w: MarkedZST) {
    consume_any(w)
}
