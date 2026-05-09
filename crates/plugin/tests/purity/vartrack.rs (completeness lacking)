use paralegal_flow::inline_test;

#[test]
fn implicit_leak() {
    inline_test! {
        pub fn main(sensitive_arg: i32) {
            let mut variable = 1;
            // Implicit flow.
            if sensitive_arg > 0 {
                variable = 2;
            }
            println!("{}", variable);
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn reassignment_leak() {
    inline_test! {
        pub fn main(sensitive_arg: i32) {
            let mut variable = sensitive_arg;
            // Implicit flow.
            if variable > 0 {
                variable = 2;
            }
            println!("{}", variable);
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn arc_leak() {
    inline_test! {
        use std::sync::{Arc, Mutex};

        pub fn main(sensitive_arg: i32) {
            let sensitive_arc = Arc::new(Mutex::new(sensitive_arg));
            let sensitive_arc_copy = sensitive_arc.clone();
            let unwrapped = *sensitive_arc_copy.lock().unwrap();
            println!("{}", unwrapped);
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn tricky_flows() {
    inline_test! {
        pub fn main(sensitive_arg: i32) {
            let mut variable = 1;
            // Implicit flow.
            if variable > 0 {
                variable = 2;
            }
            println!("{}", variable);
            if sensitive_arg > 0 {
                variable = 2;
            }
            // This call needs to be revisited.
            println!("{}", variable);
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn implicit_transmute() {
    inline_test! {
        fn leaker(a: *const i32) {
            unsafe {
                *(a as *mut _) = 42;
            }
        }

        pub fn main(sensitive_arg: i32) {
            let mut variable = 1;
            // Implicit flow.
            if variable > 0 {
                variable = 2;
            }
            leaker(&variable as *const _);
            if sensitive_arg > 0 {
                variable = 2;
            }
            // This call needs to be revisited.
            leaker(&variable as *const _);
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn non_leaky_flows() {
    inline_test! {
        pub fn main(sensitive_arg: i32) {
            let mut variable = 1;
            // Implicit flow.
            if variable > 0 {
                variable = 2;
            }
            println!("{}", variable);
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(true));
}
