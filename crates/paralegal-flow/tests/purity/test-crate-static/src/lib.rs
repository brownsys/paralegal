static mut GLOBAL_VEC: Vec<u32> = vec![];

#[paralegal::analyze]
fn mutable_static(a: u32) {
    unsafe {
        GLOBAL_VEC.push(a);
    }
}

struct PureIncrementer;

impl PureIncrementer {
    fn inc(&self, a: usize) -> usize {
        a + 1
    }
}

struct ImpureIncrementer;

impl ImpureIncrementer {
    fn inc(&self, a: usize) -> usize {
        println!("{}", a);
        a + 1
    }
}

static PURE_INCREMENTER: PureIncrementer = PureIncrementer {};
static IMPURE_INCREMENTER: ImpureIncrementer = ImpureIncrementer {};

#[paralegal::analyze]
fn pure_call_from_static(a: usize) -> usize {
    PURE_INCREMENTER.inc(a)
}

#[paralegal::analyze]
fn impure_call_from_static(a: usize) -> usize {
    IMPURE_INCREMENTER.inc(a)
}
