#[paralegal::analyze]
unsafe fn raw_mut_ptr_deref(a: usize) {
    let mut x = 42;
    let raw = &mut x as *mut i32;
    *raw = 5;
}

#[paralegal::analyze]
unsafe fn raw_mut_ptr_mut_ref(a: usize) {
    let mut x = 42;
    let raw = &mut x as *mut i32;
    let mut_ref = &mut *raw;
}

unsafe fn raw_mut_ptr_mut_ref_not_in_main_helper(a: usize) {
    let mut x = 42;
    let raw = &mut x as *mut i32;
    let mut_ref = &mut *raw;
}

#[paralegal::analyze]
fn raw_mut_ptr_mut_ref_not_in_main() {
    unsafe {
        raw_mut_ptr_mut_ref_not_in_main_helper(0);
    }
}

struct Foo {
    x: i32,
}

impl Foo {
    fn amend(&mut self) {
        self.x = 42;
    }
}

// Raw mut pointer dereference into call.
#[paralegal::analyze]
unsafe fn raw_mut_ptr_call(a: usize) {
    let mut x = Foo { x: 0 };
    let raw = &mut x as *mut Foo;
    (*raw).amend();
}

#[paralegal::analyze]
unsafe fn safe_raw_mut_ptr<'a>(a: usize) -> &'a i32 {
    let mut x = 42;
    let raw = &mut x as *mut i32;
    let immutable = *raw;
    &*raw
}

#[paralegal::analyze]
unsafe fn raw_const_ptr(a: usize) {
    let x = 42;
    let raw = &x as *const i32;
    let _points_at = *raw;
}
