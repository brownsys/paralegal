#[paralegal::marker(a)]
fn f(a: u32) -> Result<u32, &'static str> {
    if a == 7 {
        Ok(a)
    } else {
        Err("invalid number")
    }
}

#[paralegal::marker(b)]
fn g(b: u32) -> u32 {
    b
}

#[paralegal::analyze]
fn main() -> Result<u32, &'static str> {
    f(7)?;
    Ok(g(7))
}
