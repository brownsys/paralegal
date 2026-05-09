use paralegal_flow::inline_test;
use paralegal_flow::test_utils::HasGraph;

#[test]
#[ignore = "paralegal cannot resolve dyn traits"]
fn object_type_eraser() {
    inline_test! {
        trait DynamicTrait {
            fn inc(&self, a: usize) -> usize;
        }

        struct PureIncrementer;

        struct ImpureIncrementer;

        impl DynamicTrait for PureIncrementer {
            fn inc(&self, a: usize) -> usize {
                a + 1
            }
        }

        impl DynamicTrait for ImpureIncrementer {
            fn inc(&self, a: usize) -> usize {
                println!("{}", a);
                a + 1
            }
        }

        #[paralegal_flow::analyze]
        fn dyn_eraser(a: usize) -> usize {
            let dynamic: &dyn DynamicTrait = if a == 0 {
                &PureIncrementer {}
            } else {
                &ImpureIncrementer {}
            };
            dyn_eraser_helper(a, dynamic)
        }

        #[paralegal_flow::analyze]
        fn dyn_eraser_helper(a: usize, dynamic: &dyn DynamicTrait) -> usize {
            dynamic.inc(a)
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .without_entrypoint()
    .run(|graphs| {
        graphs.ctrl("dyn_eraser_helper").assert_purity(false);
        graphs.ctrl("dyn_eraser").assert_purity(false)
    })
    .unwrap()
}

#[test]
#[ignore = "paralegal cannot resolve dyn traits"]
fn return_impl_fn() {
    inline_test! {
        #[paralegal_flow::analyze]
        fn outer(a: usize) -> usize {
            let cl = hof(a);
            execute(a, &cl)
        }

        #[paralegal_flow::analyze]
        fn execute(a: usize, cl: &dyn Fn(usize) -> usize) -> usize {
            cl(a)
        }

        #[paralegal_flow::analyze]
        fn hof(a: usize) -> impl Fn(usize) -> usize {
            move |x| x + a
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .without_entrypoint()
    .run(|graphs| {
        graphs.ctrl("outer").assert_purity(true);
        graphs.ctrl("execute").assert_purity(false);
        graphs.ctrl("hof").assert_purity(true);
    })
    .unwrap()
}

#[test]
#[ignore = "paralegal cannot resolve dyn traits"]
fn passthrough_impl_fn() {
    inline_test! {
    #[paralegal_flow::analyze]
    fn outer(a: usize) -> usize {
        let cl = hof(a);
        execute(a, identity(&cl))
    }

    #[paralegal_flow::analyze]
    fn execute(a: usize, cl: &dyn Fn(usize) -> usize) -> usize {
        cl(a)
    }

    #[paralegal_flow::analyze]
    fn hof(a: usize) -> impl Fn(usize) -> usize {
        move |x| x + a
    }

    #[paralegal_flow::analyze]
    fn identity<T>(a: T) -> T {
        a
    }
    }
    .without_entrypoint()
    .with_extra_args(["--side-effect-markers"])
    .run(|graphs| {
        graphs.ctrl("outer").assert_purity(true);
        graphs.ctrl("execute").assert_purity(false);
        graphs.ctrl("hof").assert_purity(true);
        graphs.ctrl("identity").assert_purity(true);
    })
    .unwrap()
}

#[test]
#[ignore = "paralegal cannot resolve dyn traits"]
fn returns_boxed_fn() {
    inline_test! {
        #[paralegal_flow::analyze]
        fn outer(a: usize) -> usize {
            let cl = hof(a);
            execute(a, &cl)
        }

        #[paralegal_flow::analyze]
        fn execute(a: usize, cl: &dyn Fn(usize) -> usize) -> usize {
            cl(a)
        }

        #[paralegal_flow::analyze]
        fn hof(a: usize) -> Box<dyn Fn(usize) -> usize> {
            Box::new(move |x| x + a)
        }
    }
    .with_extra_args(["--side-effect-markers"])
    .without_entrypoint()
    .run(|graphs| {
        graphs.ctrl("hof").assert_purity(true);
        graphs.ctrl("execute").assert_purity(false);
        graphs.ctrl("outer").assert_purity(true);
    })
    .unwrap()
}

#[test]
#[ignore = "paralegal cannot resolve dyn traits"]
fn returns_impl_fn_with_upvars() {
    inline_test! {
        #[paralegal_flow::analyze]
        fn outer(a: usize) -> usize {
            let lam = |x| x + 1;
            let cl = hof(a, &lam);
            execute(a, &cl)
        }

        #[paralegal_flow::analyze]
        fn execute(a: usize, cl: &dyn Fn(usize) -> usize) -> usize {
            cl(a)
        }

        #[paralegal_flow::analyze]
        fn hof(a: usize, cl: &dyn Fn(usize) -> usize) -> impl Fn(usize) -> usize + '_ {
            move |x| cl(x + a)
        }
    }
    .without_entrypoint()
    .with_extra_args(["--side-effect-markers"])
    .run(|graphs| {
        graphs.ctrl("hof").assert_purity(false);
        graphs.ctrl("execute").assert_purity(false);
        graphs.ctrl("outer").assert_purity(true);
    })
    .unwrap()
}

#[test]
#[ignore = "paralegal cannot resolve dyn traits"]
fn returns_boxed_fn_with_upvars() {
    inline_test! {
        #[paralegal_flow::analyze]
        fn outer(a: usize) -> usize {
            let lam = |x| x + 1;
            let cl = hof(a, &lam);
            execute(a, &cl)
        }

        #[paralegal_flow::analyze]
        fn execute(a: usize, cl: &dyn Fn(usize) -> usize) -> usize {
            cl(a)
        }

        #[paralegal_flow::analyze]
        fn hof(a: usize, cl: &dyn Fn(usize) -> usize) -> Box<dyn Fn(usize) -> usize + '_> {
            Box::new(move |x| cl(x + a))
        }
    }
    .without_entrypoint()
    .with_extra_args(["--side-effect-markers"])
    .run(|graphs| {
        graphs.ctrl("hof").assert_purity(false);
        graphs.ctrl("execute").assert_purity(false);
        graphs.ctrl("outer").assert_purity(true);
    })
    .unwrap()
}
