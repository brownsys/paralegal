#[paralegal::analyze]
fn pure(a: usize) {
    if a > 0 {
        pure(a - 1);
    }
}

#[paralegal::analyze]
fn impure(a: usize) {
    if a > 0 {
        impure(a - 1);
    }
    println!("{}", a);
}

#[paralegal_flow::analyze]
fn mutually_recursive_pure_1(a: usize) {
    if a > 0 {
        mutually_recursive_pure_2(a - 1);
    }
}

#[paralegal_flow::analyze]
fn mutually_recursive_pure_2(a: usize) {
    if a > 0 {
        mutually_recursive_pure_1(a - 1);
    }
}

#[paralegal_flow::analyze]
fn mutually_recursive_impure_1(a: usize) {
    if a > 0 {
        mutually_recursive_impure_2(a - 1);
    }
    println!("{}", a);
}

#[paralegal_flow::analyze]
fn mutually_recursive_impure_2(a: usize) {
    if a > 0 {
        mutually_recursive_impure_1(a - 1);
    }
    println!("{}", a);
}
