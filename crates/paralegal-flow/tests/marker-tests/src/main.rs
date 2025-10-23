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

fn main() {}

use std::io::prelude::*;
use std::net::TcpStream;

#[paralegal::marker(source, return)]
fn tcp_source() -> u8 {
    42
}

#[paralegal::marker(source2, return)]
fn tcp_source2() -> u8 {
    43
}

#[paralegal::analyze]
fn side_effect_tcp_flow_in_separate_crate() -> std::io::Result<()> {
    let mut stream = TcpStream::connect("127.0.0.1:34254")?;
    let y = tcp_source2();
    stream.write(&[tcp_source()])?;
    let mut buf = [0; 128];
    stream.read(&mut buf)?;
    let _ = y + buf[0];
    Ok(())
}
