pub fn find_me(a: usize, _b: usize) -> usize {
    a
}

#[paralegal::marker(mark, return)]
pub fn source() -> usize {
    0
}

#[paralegal::marker(mark, return)]
fn taint_it<A>(_: A) -> A {
    unimplemented!()
}

pub fn assign_marker(a: usize) -> usize {
    taint_it(a)
}

pub fn find_me_generic<A>(a: A, _b: A) -> A {
    a
}

#[paralegal::marker(mark, return)]
pub fn generic_source<A>() -> A {
    unimplemented!()
}

pub fn assign_marker_generic<A>(a: A) -> A {
    taint_it(a)
}
