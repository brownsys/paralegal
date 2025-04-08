#![feature(rustc_private)]

use paralegal_flow::test_utils::*;
use paralegal_spdg::Identifier;

#[test]
fn argument_return_connection_with_field() {
    let mut test = InlineTestBuilder::new(stringify!(
        struct T {
            a: i32,
        }

        #[paralegal_flow::marker(target, return)]
        fn function<T>(t: T) -> T {
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
        assert_ne!(direct.nodes().len(), 0);
        assert_ne!(indirect.nodes().len(), 0);
        assert!(!direct.overlaps(&indirect));
    });
}

#[test]
fn argument_return_connection_non_field() {
    let mut test = InlineTestBuilder::new(stringify!(
        #[paralegal_flow::marker(target, return)]
        fn function<T>(t: T) -> T {
            t
        }

        fn main() {
            let t = 1_usize;
            let t2 = function(t);
        }
    ));
    //test.with_extra_args(["--dump".to_string(), "spdg".to_string()]);
    test.check_ctrl(|ctrl| {
        let target = ctrl.marked(Identifier::new_intern("target"));
        let direct = target.predecessors_data();
        let indirect = direct.predecessors_data();
        assert_ne!(direct.nodes().len(), 0);
        assert_ne!(indirect.nodes().len(), 0);
        assert!(!&direct.overlaps(&indirect));
    });
}
