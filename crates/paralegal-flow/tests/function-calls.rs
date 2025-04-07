#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use paralegal_flow::test_utils::*;

#[test]
fn argument_return_connection() {
    let mut test = InlineTestBuilder::new(stringify!(
        struct T {
            a: i32,
        }

        #[paralegal_flow::marker(noinline)]
        fn function(t: T) -> T {
            t
        }

        fn main() {
            let t = T { a: 1 };
            let t2 = function(t);
        }
    ));
    test.with_extra_args(["--dump".to_string(), "spdg".to_string()]);
    test.check_ctrl(|ctrl| {});
}
