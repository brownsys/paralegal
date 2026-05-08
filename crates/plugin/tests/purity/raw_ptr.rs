use paralegal_flow::{
    inline_test,
    test_utils::{DependencyEnvironment, DependencyEnvironmentBuilder},
};
use std::sync::OnceLock;

static STDLIB_ENV: OnceLock<DependencyEnvironment> = OnceLock::new();

fn stdlib_environment() -> &'static DependencyEnvironment {
    STDLIB_ENV.get_or_init(|| DependencyEnvironmentBuilder::new().with_stdlib().build())
}

#[test]
fn raw_mut_ptr_deref() {
    inline_test! {
        unsafe fn raw_mut_ptr_deref(a: usize) {
            let mut x = 42;
            let raw = &mut x as *mut i32;
            *raw = 5;
        }

        fn main() {
            unsafe {
                raw_mut_ptr_deref(0);
            }
        }
    }
    .with_dependency_environment(stdlib_environment())
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn raw_mut_ptr_mut_ref() {
    inline_test! {
        unsafe fn raw_mut_ptr_mut_ref(a: usize) {
            let mut x = 42;
            let raw = &mut x as *mut i32;
            let mut_ref = &mut *raw;
        }

        fn main() {
            unsafe {
                raw_mut_ptr_mut_ref(0);
            }
        }
    }
    .with_dependency_environment(stdlib_environment())
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn raw_mut_ptr_mut_ref_not_in_main() {
    inline_test! {
        unsafe fn raw_mut_ptr_mut_ref_not_in_main_helper(a: usize) {
            let mut x = 42;
            let raw = &mut x as *mut i32;
            let mut_ref = &mut *raw;
        }

        fn raw_mut_ptr_mut_ref_not_in_main() {
            unsafe {
                raw_mut_ptr_mut_ref_not_in_main_helper(0);
            }
        }

        fn main() {
            raw_mut_ptr_mut_ref_not_in_main();
        }
    }
    .with_dependency_environment(stdlib_environment())
    .with_extra_args(["--side-effect-markers"])
    .with_entrypoint("crate::raw_mut_ptr_mut_ref_not_in_main")
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn raw_mut_ptr_call() {
    inline_test! {
        struct Foo {
            x: i32,
        }

        impl Foo {
            fn amend(&mut self) {
                self.x = 42;
            }
        }

        unsafe fn raw_mut_ptr_call(a: usize) {
            let mut x = Foo { x: 0 };
            let raw = &mut x as *mut Foo;
            (*raw).amend();
        }

        fn main() {
            unsafe {
                raw_mut_ptr_call(0);
            }
        }
    }
    .with_dependency_environment(stdlib_environment())
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
#[ignore = "We are more conservative than scrutinizer here and disallow all raw pointers, whether they are mutable or not."]
fn safe_raw_mut_ptr() {
    inline_test! {
        unsafe fn safe_raw_mut_ptr<'a>(a: usize) -> &'a i32 {
            let mut x = 42;
            let raw = &mut x as *mut i32;
            let immutable = *raw;
            &*raw
        }

        fn main() {
            unsafe {
                safe_raw_mut_ptr(0);
            }
        }
    }
    .with_dependency_environment(stdlib_environment())
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
    });
}

#[test]
fn raw_const_ptr() {
    inline_test! {
        unsafe fn raw_const_ptr(a: usize) {
            let x = 42;
            let raw = &x as *const i32;
            let _points_at = *raw;
        }

        fn main() {
            unsafe {
                raw_const_ptr(0);
            }
        }
    }
    .with_dependency_environment(stdlib_environment())
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
    });
}
