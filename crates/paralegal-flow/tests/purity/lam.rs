use paralegal_flow::inline_test;
use paralegal_flow::test_utils::HasGraph;

#[test]
fn closure_tests() {
    inline_test! {
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

        pub fn main(a: usize) {
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
    }
    .with_extra_args(["--side-effect-markers"])
    .run(|graphs| {
        graphs.ctrl("main").assert_purity(true);
    })
    .unwrap()
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
