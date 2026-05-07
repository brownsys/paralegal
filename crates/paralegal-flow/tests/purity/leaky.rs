use paralegal_flow::{inline_test, test_utils::*};

#[test]
fn print() {
    inline_test! {
        fn main(left: usize, right: usize) -> usize {
            println!("{} {}", left, right);
            left + right
        }
    }
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn network() {
    inline_test! {
        use std::net::UdpSocket;

        fn main(socket: &UdpSocket, buf: &[u8]) -> std::io::Result<usize> {
            socket.send(&buf)
        }
    }
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn interior() {
    inline_test! {
        use std::cell::RefCell;

        pub fn main(refcell: &RefCell<usize>) {
            *refcell.borrow_mut() = 10;
        }
    }
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
#[ignore = "We don't support this yet"]
fn implicit() {
    inline_test! {
        struct CustomSmartPointer {
            data: usize,
        }

        impl Drop for CustomSmartPointer {
            fn drop(&mut self) {
                println!("Dropping CustomSmartPointer with data `{}`!", self.data);
            }
        }

        fn main() {
            let _sp = CustomSmartPointer { data: 42 };
        }
    }
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn transmute_struct() {
    inline_test! {
        struct StructImmut<'a> {
            field: &'a u32,
        }

        struct StructMut<'a> {
            field: &'a mut u32,
        }

        fn main(value: u32, sink: StructImmut) {
            let sink_mut: StructMut = unsafe { std::mem::transmute(sink) };
            *sink_mut.field = value;
        }
    }
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}

#[test]
fn transmute_arr() {
    inline_test! {
        fn main(value: u32, sink: [&u32; 1]) {
            let sink_mut: [&mut u32; 1] = unsafe { std::mem::transmute(sink) };
            *sink_mut[0] = value;
        }
    }
    .with_dependency_environment(super::stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(false);
    });
}
