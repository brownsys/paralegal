use paralegal_flow::inline_test;

#[test]
fn raw_mut_ptr_deref() {
    inline_test! {
        pub unsafe fn main(a: usize) {
            let mut x = 42;
            let raw = &mut x as *mut i32;
            *raw = 5;
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn raw_mut_ptr_mut_ref() {
    inline_test! {
        pub unsafe fn main(a: usize) {
            let mut x = 42;
            let raw = &mut x as *mut i32;
            let mut_ref = &mut *raw;
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn raw_mut_ptr_mut_ref_not_in_main() {
    inline_test! {
        pub unsafe fn helper(a: usize) {
            let mut x = 42;
            let raw = &mut x as *mut i32;
            let mut_ref = &mut *raw;
        }

        fn main() {
            unsafe {
                helper(0);
            }
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn raw_mut_ptr_call() {
    inline_test! {
        #[derive(Debug)]
        struct Foo {
            x: i32
        }

        impl Foo {
            fn amend(&mut self) {
                self.x = 42;
            }
        }
        // Raw mut pointer dereference into call.
        pub unsafe fn main(a: usize) {
            let mut x = Foo { x: 0 };
            let raw = &mut x as *mut Foo;
            (*raw).amend();
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn safe_raw_mut_ptr() {
    inline_test! {
        pub unsafe fn main<'a>(a: usize) -> &'a i32 {
            let mut x = 42;
            let raw = &mut x as *mut i32;
            let immutable = *raw;
            &*raw
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(true));
}

#[test]
fn raw_const_ptr() {
    inline_test! {
        pub unsafe fn main(a: usize) {
            let x = 42;
            let raw = &x as *const i32;
            let _points_at = *raw;
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(true));
}
