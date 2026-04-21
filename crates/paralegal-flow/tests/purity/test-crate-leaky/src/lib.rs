#[paralegal::analyze]
pub fn print(left: usize, right: usize) -> usize {
    println!("{} {}", left, right);
    left + right
}

use std::io;
use std::net::UdpSocket;

#[paralegal::analyze]
pub fn network(socket: &UdpSocket, buf: &[u8]) -> io::Result<usize> {
    socket.send(buf)
}

use std::cell::RefCell;

#[paralegal::analyze]
pub fn interior(refcell: &RefCell<usize>) {
    *refcell.borrow_mut() = 10;
}

struct CustomSmartPointer {
    data: usize,
}

impl Drop for CustomSmartPointer {
    fn drop(&mut self) {
        println!("Dropping CustomSmartPointer with data `{}`!", self.data);
    }
}

#[paralegal::analyze]
pub fn implicit(data: usize) {
    let sp = CustomSmartPointer { data };
}

use std::ptr;

#[paralegal_flow::analyze]
unsafe fn intrinsic_leaker(value: &u64, sink: &u64) {
    let sink = sink as *const u64;
    ptr::copy(value as *const u64, sink as *mut u64, 1);
}

struct StructImmut<'a> {
    field: &'a u32,
}

struct StructMut<'a> {
    field: &'a mut u32,
}

#[paralegal_flow::analyze]
fn transmute_struct(value: u32, sink: StructImmut) {
    let sink_mut: StructMut = unsafe { std::mem::transmute(sink) };
    *sink_mut.field = value;
}

#[paralegal_flow::analyze]
fn transmute_arr(value: u32, sink: [&u32; 1]) {
    let sink_mut: [&mut u32; 1] = unsafe { std::mem::transmute(sink) };
    *sink_mut[0] = value;
}
