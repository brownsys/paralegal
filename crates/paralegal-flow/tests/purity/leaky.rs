use paralegal_flow::inline_test;
use paralegal_flow::test_utils::HasGraph;

#[test]
fn print() {
    inline_test! {
        pub fn main(left: usize, right: usize) -> usize {
            println!("{} {}", left, right);
            left + right
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn network() {
    inline_test! {
        use std::io;
        use std::net::UdpSocket;

        pub fn main(socket: &UdpSocket, buf: &[u8]) -> io::Result<usize> {
            socket.send(buf)
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn interior() {
    inline_test! {
        use std::cell::RefCell;

        pub fn main(refcell: &RefCell<usize>) {
            *refcell.borrow_mut() = 10;
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
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

        pub fn main(data: usize) {
            let sp = CustomSmartPointer { data };
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .check_ctrl(|ctrl| ctrl.assert_purity(false));
}

#[test]
fn adversarial() {
    inline_test! {
        use std::ptr;

        #[paralegal_flow::analyze]
        unsafe fn intrinsic_leaker(value: &u64, sink: &u64) {
            let sink = sink as *const u64;
            ptr::copy(value as *const u64, sink as *mut u64, 1);
        }

        struct StructImmut<'a> {
            field: &'a u32,
        }

        struct StructMut<'a> {
            field: &'a mut u32,
        }

        #[paralegal_flow::analyze]
        fn transmute_struct(value: u32, sink: StructImmut) {
            let sink_mut: StructMut = unsafe { std::mem::transmute(sink) };
            *sink_mut.field = value;
        }

        #[paralegal_flow::analyze]
        fn transmute_arr(value: u32, sink: [&u32; 1]) {
            let sink_mut: [&mut u32; 1] = unsafe { std::mem::transmute(sink) };
            *sink_mut[0] = value;
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .without_entrypoint()
    .run(|graphs| {
        graphs.ctrl("transmute_struct").assert_purity(false);
        graphs.ctrl("transmute_arr").assert_purity(false);
        graphs.ctrl("intrinsic_leaker").assert_purity(false);
    })
    .unwrap()
}
