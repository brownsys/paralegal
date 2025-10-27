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
fn side_effect_tcp_flow() -> std::io::Result<()> {
    let mut stream = TcpStream::connect("127.0.0.1:34254")?;
    let y = tcp_source2();
    stream.write(&[tcp_source()])?;
    let mut buf = [0; 128];
    stream.read(&mut buf)?;
    let _ = y + buf[0];
    Ok(())
}

#[paralegal::analyze]
fn side_effect_vec() {
    let mut v = vec![0];
    v.push(1);
    v.pop();
}

extern "C" {
    fn plus(a: i32, b: i32) -> i32;
}

#[paralegal::marker(source, return)]
fn source() -> i32 {
    42
}

#[paralegal::marker(source2, return)]
fn source2() -> i32 {
    43
}

#[paralegal::analyze]
fn side_effect_extern_flow() -> std::io::Result<()> {
    let x = source2();
    let z = source();
    let y = plus(z, 3);
    let result = y + x;
    Ok(())
}

#[paralegal::analyze]
fn side_effect_extern() -> std::io::Result<()> {
    let x = 2;
    let y = plus(3, x);
    Ok(())
}

#[paralegal::analyze]
fn side_effect_empty() -> std::io::Result<()> {
    Ok(())
}

#[paralegal::analyze]
fn side_effect_add() -> std::io::Result<()> {
    let x = 2;
    let y = 3 + x;
    Ok(())
}

#[paralegal::analyze]
fn side_effect_tcp() -> std::io::Result<()> {
    let mut stream = TcpStream::connect("127.0.0.1:34254")?;

    stream.write(&[1])?;
    stream.read(&mut [0; 128])?;
    Ok(())
}
