#[paralegal::marker(source, return)]
fn source() -> usize {
    0
}

#[paralegal::marker(pass, arguments = [0])]
fn pass<T>(t: T) -> T {
    t
}

#[paralegal::marker(target, arguments = [0])]
fn target(i: usize) {}

#[paralegal::analyze]
fn thread_spawn() {
    let src = source();
    let next = std::thread::spawn(move || pass(src)).join().unwrap();
    target(next);
}

fn main() {}
