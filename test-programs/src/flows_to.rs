#[paralegal::analyze]
#[paralegal::marker(private_key, arguments = [0])]
fn f(a: u32) -> u32 {
    g(7)
}

#[paralegal::marker(encrypt_func, arguments = [0])]
fn g(b: u32) -> u32 {
    b
}

fn main() {
    f(7);
}
