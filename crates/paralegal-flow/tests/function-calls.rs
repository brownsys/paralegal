#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use paralegal_flow::test_utils::*;
use paralegal_spdg::Identifier;

#[test]
fn argument_return_connection() {
    let mut test = InlineTestBuilder::new(stringify!(
        struct T {
            a: i32,
        }

        #[paralegal_flow::marker(target, return)]
        fn function(t: T) -> T {
            t
        }

        fn main() {
            let t = T { a: 1 };
            let t2 = function(t);
        }
    ));
    //test.with_extra_args(["--dump".to_string(), "spdg".to_string()]);
    test.check_ctrl(|ctrl| {
        let target = ctrl.marked(Identifier::new_intern("target"));
        let direct = target.predecessors_data();
        let indirect = direct.predecessors_data();
        assert!(&direct.overlaps(&indirect));
    });
}
