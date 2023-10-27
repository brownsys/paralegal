fn inner() -> u32 {
    0
}

fn elide_me(i: u32) -> u32 {
    std::convert::identity(i)
}

fn elide_me2(i: &mut u32) {
    *i = std::convert::identity(*i);
}

#[paralegal::analyze]
fn basic_elision() {
    let inp = input();
    receive_touched(elide_me(inp))
}

#[paralegal::analyze]
fn basic_elision_mut() {
    let mut inp = input();
    elide_me2(&mut inp);
    receive_touched(inp);
}

fn not_elided() -> u32 {
    other_input()
}

#[paralegal::analyze]
fn unelision() {
    receive_touched(not_elided());
}

#[paralegal::marker(noinline)]
fn other_input() -> u32 {
    9
}

#[paralegal::marker(noinline)]
fn receive_touched<T>(t: T) {
}

#[paralegal::marker(noinline)]
fn receive_untouched<T>(t: T) {
}

fn elided<T, B>(t: T, b: B) -> (T, B) {
    (t, b)
}

fn elided2<T, B>(t: (T, B)) -> (T, B) {
    t
}

fn elided3<T>(t: &mut T) {
}

#[paralegal::marker(noinline)]
fn input() -> u32 {
    8
}

#[paralegal::analyze]
fn connection_precision() {
    let touched = input();
    let untouched = other_input();
    let (touched, untouched) = elided(touched, untouched);
    receive_touched(touched);
    receive_untouched(untouched);
}

#[paralegal::analyze]
fn connection_precision_2() {
    let touched = input();
    let untouched = other_input();
    let (touched, untouched) = elided2((touched, untouched));
    receive_touched(touched);
    receive_untouched(untouched);
}


#[paralegal::analyze]
fn connection_precision_3() {
    let touched = input();
    let untouched = other_input();
    let mut t = (touched, untouched);
    elided3(&mut t);
    receive_touched(touched);
    receive_untouched(untouched);
}

struct S {
    touched: u32,
    untouched: u32,
}

impl S {
    fn elided4(&mut self) {
        self.touched += self.untouched
    }
}

#[paralegal::analyze]
fn connection_precision_self() {
    let touched = input();
    let untouched = other_input();
    let mut s = S {
        touched, untouched
    };
    s.elided4();
    receive_touched(s.touched);
    receive_untouched(s.untouched);
}



#[paralegal::analyze]
fn no_elision_without_input() {
    let v = inner();
    receive_touched(v);
}


fn do_io<T>(v: T) {}

#[paralegal::analyze]
fn no_elision_without_output() {
    let v = input();
    do_io(v);
}

fn elided5(touched: u32, untouched: u32, arg1: &mut u32) -> u32 {
    *arg1 = touched;
    untouched
}

#[paralegal::analyze]
fn connection_precision_args() {
    let touched = input();
    let untouched = other_input();
    let mut arg1 = 0;
    let arg2 = elided5(touched, untouched, &mut arg1);
    receive_touched(arg1);
    receive_untouched(arg2);
}


fn main() {}