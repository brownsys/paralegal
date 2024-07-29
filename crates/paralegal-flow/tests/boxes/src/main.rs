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
fn ref_with_checkpoint() {
    let mut inp = source();
    let r = checkpoint_2(&mut inp);
    ***r += modifier();
    sink(inp);
}

#[paralegal::analyze]
fn strong_box_update() {
    let mut inp = Box::new(source_2());
    let r = &mut inp;
    **r = modifier();
    sink(inp);
}

#[paralegal::analyze]
fn strong_ref_in_box_update() {
    let mut src = source_2();
    let mut inp = Box::new(&mut src);
    **inp = modifier();
    sink(src);
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
fn ref_mut_box() {
    let mut inp = Box::new(source_2());
    let my_ref = &mut inp;

    **my_ref += modifier();
    sink(inp);
}

#[paralegal::analyze]
fn box_ref_mut() {
    let mut src = source_2();
    let mut inp = Box::new(&mut src);

    **inp += modifier();
    sink(src);
}

fn main() {}
