type F = usize;
#[paralegal::marker(source, return)]
fn source() -> Box<F> {
    unreachable!()
}

#[paralegal::marker(checkpoint, return)]
fn checkpoint<T>(_: T) -> Box<F> {
    unreachable!()
}

#[paralegal::marker(sink, arguments = [0])]
fn sink<T>(_: T) {}

#[paralegal::analyze]
fn simple_overtaint() {
    sink(checkpoint(source()))
}

#[paralegal::marker(checkpoint_2, return)]
fn checkpoint_2<T>(i: T) -> Box<T> {
    Box::new(i)
}

#[paralegal::marker(modifier, return)]
fn modifier() -> usize {
    6
}

#[paralegal::analyze]
fn box_mut_ref() {
    let mut inp = source();
    let r = checkpoint_2(&mut inp);
    ***r += modifier();
    sink(inp);
}

#[paralegal::marker(source_2, return)]
fn source_2() -> usize {
    0
}

#[paralegal::analyze]
fn field_ref() {
    let mut inp = (source_2(),);
    let my_ref = &mut inp;

    my_ref.0 += modifier();
    sink(inp);
}

#[paralegal::analyze]
fn simple_box_mut_ref() {
    let mut inp = Box::new(source_2());
    let my_ref = &mut inp;

    **my_ref += modifier();
    sink(inp);
}
