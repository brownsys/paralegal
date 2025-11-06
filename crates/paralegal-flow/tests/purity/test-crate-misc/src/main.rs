use std::io::prelude::*;
use std::net::TcpStream;

#[paralegal::marker(source, return)]
fn tcp_source() -> u8 {
    42
}

#[paralegal::marker(source2, return)]
fn tcp_source2() -> u8 {
    43
}

#[paralegal::analyze]
fn side_effect_tcp_flow() -> std::io::Result<()> {
    let mut stream = TcpStream::connect("127.0.0.1:34254")?;
    let y = tcp_source2();
    stream.write(&[tcp_source()])?;
    let mut buf = [0; 128];
    stream.read(&mut buf)?;
    let _ = y + buf[0];
    Ok(())
}

#[paralegal::analyze]
fn side_effect_vec() {
    let mut v = vec![0];
    v.push(1);
    v.pop();
}

extern "C" {
    fn plus(a: i32, b: i32) -> i32;
}

#[paralegal::marker(source, return)]
fn source() -> i32 {
    42
}

#[paralegal::marker(source2, return)]
fn source2() -> i32 {
    43
}

#[paralegal::analyze]
fn side_effect_extern_flow() -> std::io::Result<()> {
    let x = source2();
    let z = source();
    let y = plus(z, 3);
    let result = y + x;
    Ok(())
}

#[paralegal::analyze]
fn side_effect_extern() -> std::io::Result<()> {
    let x = 2;
    let y = plus(3, x);
    Ok(())
}

#[paralegal::analyze]
fn side_effect_empty() -> std::io::Result<()> {
    Ok(())
}

#[paralegal::analyze]
fn side_effect_add() -> std::io::Result<()> {
    let x = 2;
    let y = 3 + x;
    Ok(())
}

#[paralegal::analyze]
fn side_effect_tcp() -> std::io::Result<()> {
    let mut stream = TcpStream::connect("127.0.0.1:34254")?;

    stream.write(&[1])?;
    stream.read(&mut [0; 128])?;
    Ok(())
}

pub fn lambda_called(a: usize) -> usize {
    let l = |x| {
        return x * x;
    };

    l(a)
}

pub fn lambda_uncalled(a: usize) -> usize {
    let _l = |x: usize| -> usize {
        return x * x;
    };
    a
}

#[inline(never)]
pub fn execute_once<F: FnOnce(usize) -> usize>(x: usize, l: F) -> usize {
    l(x)
}

#[inline(never)]
pub fn execute_mut<F: FnMut(usize) -> usize>(x: usize, mut l: F) -> usize {
    l(x)
}

#[inline(never)]
pub fn execute<F: Fn(usize) -> usize>(x: usize, l: F) -> usize {
    l(x)
}

// // This is an example of dynamic dispatch, which does not let compiler determine the type of l.
// #[pear::scrutinizer_impure]
// pub fn execute_dyn(x: usize, l: &dyn Fn(usize) -> usize) -> usize {
//     l(x)
// }

#[paralegal::analyze]
pub fn closure_tests(a: usize) {
    let lambda = |x: usize| -> usize {
        return x * x;
    };

    let capture_param = 42;
    let closure_capture = |x: usize| -> usize {
        return x * capture_param;
    };

    let capture_move_param = 42;
    let closure_capture_move = move |x: usize| -> usize {
        return x * capture_move_param;
    };

    let ambiguous_lambda = if a > 5 {
        |x: usize| -> usize {
            return x;
        }
    } else {
        |x: usize| -> usize {
            return x * x;
        }
    };

    execute_once(a, lambda);
    execute_once(a, closure_capture);
    execute_once(a, closure_capture_move);
    execute_once(a, ambiguous_lambda);

    execute_mut(a, lambda);
    execute_mut(a, closure_capture);
    execute_mut(a, closure_capture_move);
    execute_mut(a, ambiguous_lambda);

    execute(a, lambda);
    execute(a, closure_capture);
    execute(a, closure_capture_move);
    execute(a, ambiguous_lambda);

    // execute_dyn(a, &lambda);
    // execute_dyn(a, &closure_capture);
    // execute_dyn(a, &closure_capture_move);
    // execute_dyn(a, &ambiguous_lambda);
}

// mod resolving_opaque {
//     #[pear::scrutinizer_impure]
//     pub fn partially_opaque(
//         sensitive_attr: usize,
//         flag: bool,
//         l1: &dyn Fn(usize) -> usize,
//     ) -> usize {
//         let l2 = |x: usize| -> usize {
//             return x * x;
//         };

//         let lambda = if flag { l1 } else { &l2 };

//         lambda(sensitive_attr)
//     }

//     #[pear::scrutinizer_pure]
//     pub fn resolved_partially_opaque(sensitive_attr: usize, flag: bool) -> usize {
//         let lambda = |x: usize| -> usize {
//             return x * x;
//         };

//         partially_opaque(sensitive_attr, flag, &lambda)
//     }
// }
//
extern "C" {
    fn foo() -> i32;
}
struct MyStruct;

impl MyStruct {
    pub fn bar() -> i32 {
        unsafe { foo() }
    }
}

struct OtherStruct;

impl OtherStruct {
    pub fn bar() -> i32 {
        unsafe { foo() }
    }
}

#[paralegal::analyze]
fn annotation_test_impl_pure() {
    MyStruct::bar();
}

#[paralegal::analyze]
fn annotation_test_impl_impure() {
    OtherStruct::bar();
}

mod my_mod {
    extern "C" {
        fn foo() -> i32;
    }

    pub fn bar() -> i32 {
        unsafe { foo() }
    }

    pub struct NestedStruct;

    impl NestedStruct {
        pub fn bar() -> i32 {
            unsafe { foo() }
        }
    }
}

#[paralegal::analyze]
fn annotation_test_nested_impl_pure() {
    my_mod::NestedStruct::bar();
}

#[paralegal::analyze]
fn annotation_test_mod_pure() {
    my_mod::bar();
}

mod other_mod {
    extern "C" {
        fn foo() -> i32;
    }

    pub fn bar() -> i32 {
        unsafe { foo() }
    }

    pub struct NestedStruct;

    impl NestedStruct {
        pub fn bar() -> i32 {
            unsafe { foo() }
        }
    }
}

#[paralegal::analyze]
fn annotation_test_mod_impure() {
    other_mod::bar();
}

#[paralegal::analyze]
fn annotation_test_nested_impl_impure() {
    other_mod::NestedStruct::bar();
}

#[paralegal::analyze]
fn clone_unit_test() {
    ().clone()
}

fn wrapper() {
    ().clone()
}

#[paralegal::analyze]
fn clone_unit_test_wrapped() {
    wrapper()
}

struct Foo {
    a: usize,
    b: &'static str,
    c: bool,
}

#[paralegal::analyze]
fn structs(a: usize) {
    let mut foo = Foo {
        a,
        b: "hello",
        c: true,
    };
    foo.a = 30;
    foo.b = "hello2";
}
