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

pub fn hof(f: impl FnOnce(usize)) {
    let input = generic_source();
    f(input)
}

#[paralegal::marker(incoming, arguments = [0])]
fn accept_donation(i: String) {}

pub trait Donator {
    fn donate(&self) -> String;
}

pub fn exercise_donate(d: &impl Donator) {
    accept_donation(d.donate())
}

pub trait Receiver {
    fn receive(&self, value: String);
}

pub fn exercise_receive(r: &impl Receiver) {
    r.receive(generic_source())
}
