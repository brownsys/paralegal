#![feature(rustc_private)]

use paralegal_flow::{inline_test, test_utils::*};

const EXTRA_ARGS: [&str; 1] = ["--no-interprocedural-analysis"];

#[test]
fn return_is_tracked() {
    inline_test! {
        #[paralegal_flow::marker(noinline, return)]
        fn input() -> i32 { 0 }
        #[paralegal_flow::marker(noinline, return)]
        fn output(_i: i32) -> i32 { 0 }
        fn main() -> i32 { output(input()) }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("input");
        let get = graph.call_site(&get_fn);
        let send_fn = graph.function("output");
        let send = graph.call_site(&send_fn);

        assert!(graph.returns(&send.output()));
        assert!(graph.returns(&get.output()));
    });
}

#[test]
fn simple_happens_before_has_connections() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(noinline, return)]
        fn dp_user_data(user_data: &mut UserData) {}

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(user_data: &UserData) {}

        fn main() {
            let mut user_data = get_user_data();
            dp_user_data(&mut user_data);
            send_user_data(&user_data);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let dp_fn = graph.function("dp_user_data");
        let dp = graph.call_site(&dp_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);

        assert!(get.output().flows_to_data(&dp.input()));
        assert!(dp.output().flows_to_data(&send.input()));
        assert!(get.output().flows_to_data(&send.input()));
        assert!(
            dbg!(get.output()).always_happens_before_data(&dbg!(dp.output()), &dbg!(send.input()),)
        )
    });
}

#[test]
fn happens_before_if_has_connections() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(noinline, return)]
        fn dp_user_data(user_data: &mut UserData) {}

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(user_data: &UserData) {}

        fn main(cond: bool) {
            let mut user_data = get_user_data();
            if cond {
                dp_user_data(&mut user_data);
            }
            send_user_data(&user_data);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let dp_fn = graph.function("dp_user_data");
        let dp = graph.call_site(&dp_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);
        assert!(get.output().flows_to_data(&dp.input()));
        assert!(dp.output().flows_to_data(&send.input()));
        assert!(get.output().flows_to_data(&send.input()));
        assert!(
            !get.output()
                .always_happens_before_data(&dp.output(), &send.input(),)
        );
    });
}

#[test]
fn data_influenced_conditional_happens_before() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(noinline, return)]
        fn dp_user_data(user_data: &mut UserData) {}

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(user_data: &UserData) {}

        #[paralegal_flow::marker(noinline, return)]
        fn data_contains_3(d: &UserData) -> bool { false }

        fn main() {
            let mut user_data = get_user_data();
            if data_contains_3(&user_data) {
                dp_user_data(&mut user_data);
            }
            send_user_data(&user_data);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let dp_fn = graph.function("dp_user_data");
        let dp = graph.call_site(&dp_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);
        assert!(get.output().flows_to_data(&dp.input()));
        assert!(dp.output().flows_to_data(&send.input()));
        assert!(get.output().flows_to_data(&send.input()));
    });
}

#[test]
fn conditional_happens_before_with_two_parents_before_if() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data_with(data: Vec<i64>) -> UserData { UserData { data } }

        #[paralegal_flow::marker(noinline, return)]
        fn dp_user_data(user_data: &mut UserData) {}

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(user_data: &UserData) {}

        fn main(mut d: Vec<i64>, cond: bool) {
            d.push(6);
            let mut user_data = get_user_data_with(d);
            if cond {
                dp_user_data(&mut user_data);
            }
            send_user_data(&user_data);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data_with");
        let get = graph.call_site(&get_fn);
        let dp_fn = graph.function("dp_user_data");
        let dp = graph.call_site(&dp_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);
        let push_fn = graph.function("push");
        let push = graph.call_site(&push_fn);
        assert!(push.output().flows_to_data(&get.input()));
        assert!(get.output().flows_to_data(&dp.input()));
        assert!(dp.output().flows_to_data(&send.input()));
        assert!(get.output().flows_to_data(&send.input()));
        assert!(
            push.output()
                .always_happens_before_data(&get.output(), &send.input(),)
        );
        assert!(
            !push
                .output()
                .always_happens_before_data(&dp.output(), &send.input(),)
        );
    });
}

#[test]
fn loops() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(noinline, return)]
        fn dp_user_data(user_data: &mut UserData) {}

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(user_data: &UserData) {}

        fn main(mut x: i32) {
            let mut user_data = get_user_data();
            while x < 10 {
                dp_user_data(&mut user_data);
                x -= 1;
            }
            send_user_data(&user_data);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let dp_fn = graph.function("dp_user_data");
        let dp = graph.call_site(&dp_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);
        assert!(get.output().flows_to_data(&dp.input()));
        assert!(dp.output().flows_to_data(&send.input()));
        assert!(get.output().flows_to_data(&send.input()));
    });
}

#[test]
fn loop_retains_dependency() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(noinline, return)]
        fn get_other_data() -> Vec<i64> { vec![] }

        fn dp_user_data_with(user_data: &mut UserData, other_data: &Vec<i64>) {}

        fn modify_other_data(other_data: &mut Vec<i64>) {}

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(user_data: &UserData) {}

        fn main(mut x: i32) {
            let mut user_data = get_user_data();
            let mut other_data = get_other_data();
            while x < 10 {
                dp_user_data_with(&mut user_data, &other_data);
                modify_other_data(&mut other_data);
                x -= 1;
            }
            send_user_data(&user_data);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let get_other_fn = graph.function("get_other_data");
        let get_other = graph.call_site(&get_other_fn);
        let dp_fn = graph.function("dp_user_data_with");
        let dp = graph.call_site(&dp_fn);
        let modify_other_fn = graph.function("modify_other_data");
        let modify_other = graph.call_site(&modify_other_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);

        assert!(get.output().flows_to_data(&dp.input()));
        assert!(get_other.output().flows_to_data(&dp.input()));
        assert!(modify_other.output().flows_to_data(&dp.input()));
        assert!(dp.output().flows_to_data(&send.input()));
        assert!(dbg!(modify_other.output()).flows_to_data(&dbg!(send.input())));
        assert!(get.output().flows_to_data(&send.input()));
    });
}

#[test]
fn modify_pointer() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(noinline, return)]
        fn modify_vec(v: &mut [i64]) {}

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(user_data: &UserData) {}

        fn main() {
            let ref mut p = get_user_data();
            modify_vec(&mut p.data);
            send_user_data(p);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let create_fn = graph.function("modify_vec");
        let create = graph.call_site(&create_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);

        assert!(dbg!(get.output()).flows_to_data(&create.input()));
        assert!(create.output().flows_to_data(&dbg!(send.input())));
        assert!(get.output().flows_to_data(&send.input()));
    });
}

#[test]
fn on_mut_var() {
    inline_test! {
        #[paralegal_flow::marker(hello, return)]
        fn source() -> i32 { 0 }

        #[paralegal_flow::marker(noinline, return)]
        fn modify_it(x: &mut i32) {}

        #[paralegal_flow::marker(there, arguments = [0])]
        fn receiver(x: i32) {}

        fn main() {
            let mut x = source();
            modify_it(&mut x);
            receiver(x);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let source_fn = graph.function("source");
        let source = graph.call_site(&source_fn);
        let modify_fn = graph.function("modify_it");
        let modify = graph.call_site(&modify_fn);
        let receive_fn = graph.function("receiver");
        let receive = graph.call_site(&receive_fn);

        assert!(source.output().flows_to_data(&modify.input()));
        assert!(modify.output().flows_to_data(&receive.input()));
    });
}

#[test]
#[ignore = "Returning references has undecided PDG semantics. See \
    https://github.com/willcrichton/flowistry/issues/90"]
fn spurious_connections_in_deref() {
    inline_test! {
        struct S {}
        struct T {}

        #[paralegal_flow::marker(noinline, return)]
        fn new_s() -> S { S {} }

        impl std::ops::Deref for S {
            type Target = T;
            #[paralegal_flow::marker(noinline, return)]
            fn deref(&self) -> &T { unimplemented!() }
        }

        #[paralegal_flow::marker(noinline, return)]
        fn read_t(_t: &T) {}

        fn main() {
            let s = new_s();
            let t: &T = &*s;
            read_t(t);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let source_fn = graph.function("new_s");
        let source = graph.call_site(&source_fn);
        let modify_fn = graph.function("deref");
        let modify = graph.call_site(&modify_fn);
        let receive_fn = graph.function("read_t");
        let receive = graph.call_site(&receive_fn);
        assert!(source.output().flows_to_data(&modify.input()));
        assert!(modify.output().flows_to_data(&receive.input()));
        assert!(
            source
                .output()
                .always_happens_before_data(&modify.output(), &receive.input(),)
        )
    });
}

#[test]
fn control_flow_tracking_overtaint() {
    inline_test! {
        #[paralegal_flow::marker(noinline, return)]
        fn input() -> i32 { 0 }

        #[paralegal_flow::marker(hello, return)]
        fn source() -> i32 { 0 }

        struct S;

        #[paralegal_flow::marker(noinline, return)]
        fn new_s() -> S { S }

        #[paralegal_flow::marker(noinline, return)]
        fn read_t(_s: &S) {}

        fn main() {
            let early_val = input();
            let late_val = source();
            let a_val = new_s();
            if early_val > 9 {
                if late_val < 70 {
                    read_t(&a_val);
                }
            }
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let early_val_fn = graph.function("input");
        let early_val = graph.call_site(&early_val_fn);
        let late_val_fn = graph.function("source");
        let late_val = graph.call_site(&late_val_fn);
        let read_fn = graph.function("read_t");
        let read = graph.call_site(&read_fn);
        assert!(late_val.output().influences_ctrl(&read.input()));
        assert!(dbg!(early_val.output()).influences_ctrl(&dbg!(read.input())));
    });
}

#[test]
fn control_flow_tracking_for_non_fn_compound_conditions() {
    inline_test! {
        struct S;

        #[paralegal_flow::marker(noinline, return)]
        fn new_s() -> S { S }

        #[paralegal_flow::marker(noinline, return)]
        fn input() -> i32 { 0 }

        #[paralegal_flow::marker(hello, return)]
        fn source() -> i32 { 0 }

        #[paralegal_flow::marker(noinline, return)]
        fn read_t(_s: &S) {}

        fn main() {
            let a_val = new_s();
            let another_thing = input();
            // This also works with a simpler condition (e.g. `false`) after the `&&`,
            // but I want to avoid the potential of a compiler optimization getting
            // clever and making this pass, hence the complexity.
            if source() > 8 && another_thing < 9 {
                read_t(&a_val);
            }
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let cond_input_fn = graph.function("new_s");
        let cond_input = graph.call_site(&cond_input_fn);
        let other_cond_fn = graph.function("input");
        let other_cond = graph.call_site(&other_cond_fn);
        let read_fn = graph.function("read_t");
        let read = graph.call_site(&read_fn);
        assert!(cond_input.output().flows_to_data(&read.input()));
        assert!(!other_cond.output().flows_to_data(&read.input()));
        // SOUNDNESS: The previous assertion establishes that we can't get there
        // with data only, so this next check *must* involve a control edge
        assert!(cond_input.output().flows_to_any(&read.input()));
        assert!(other_cond.output().influences_ctrl(&read.input()));
    });
}

#[test]
#[ignore = "https://github.com/brownsys/paralegal/issues/168"]
fn control_flow_tracking_for_compound_cond_with_fun() {
    inline_test! {
        struct S;

        #[paralegal_flow::marker(noinline, return)]
        fn new_s() -> S { S }

        #[paralegal_flow::marker(hello, return)]
        fn source() -> i32 { 0 }

        #[paralegal_flow::marker(noinline, return)]
        fn input() -> i32 { 0 }

        #[paralegal_flow::marker(noinline, return)]
        fn read_t(_s: &S) {}

        fn main() {
            let a_val = new_s();
            if source() > 8 && input() < 9 {
                read_t(&a_val);
            }
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let cond_input_fn = graph.function("source");
        let cond_input = graph.call_site(&cond_input_fn);
        let other_cond_fn = graph.function("input");
        let other_cond = graph.call_site(&other_cond_fn);
        let read_fn = graph.function("read_t");
        let read = graph.call_site(&read_fn);
        assert!(cond_input.output().influences_ctrl(&read.input()));
        assert!(other_cond.output().influences_ctrl(&read.input()));
        // SOUNDNESS: Now that we only track data we must understand the control flow
        // influence on a function call as control flow influence of its return value.
        // Also theoretically we should explicitly check that return value here
        // instead of all outputs, but the function in the test case does not have
        // any (mutable) arguments.
        assert!(cond_input.output().influences_ctrl(&other_cond.output()));
        // The finer grained SPDG no longer shows these as neighbors, so they're only
        // checked as paths
        // assert!(cond_input.output().is_neighbor_ctrl(&other_cond.input()));
        // assert!(other_cond.output().is_neighbor_ctrl(&read.input()));
        assert!(cond_input.output().influences_ctrl(&other_cond.output()));
        // Not sure why this ever worked and if it is even the correct semantics
        // assert!(!cond_input.output().is_neighbor_ctrl(&read.input()));
    });
}

#[test]
#[ignore = "This was for testing async desugaring (https://github.com/brownsys/paralegal/issues/168) but actually this shouldn't work."]
fn and_desugaring_similar_pattern() {
    inline_test! {
        struct S;

        #[paralegal_flow::marker(noinline, return)]
        fn new_s() -> S { S }

        #[paralegal_flow::marker(noinline, return)]
        fn input() -> i32 { 0 }

        #[paralegal_flow::marker(hello, return)]
        fn source() -> i32 { 0 }

        #[paralegal_flow::marker(noinline, return)]
        fn read_t(_s: &S) {}

        fn main() {
            let a_val = new_s();
            let first_dep = input();
            let mut second_dep: i32;
            if first_dep == 8 {
                second_dep = source();
            } else {
                second_dep = 0;
            }
            if second_dep > 9 {
                read_t(&a_val);
            }
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let cond_input_fn = graph.function("input");
        let cond_input = graph.call_site(&cond_input_fn);
        let other_cond_fn = graph.function("source");
        let other_cond = graph.call_site(&other_cond_fn);
        let read_fn = graph.function("read_t");
        let read = graph.call_site(&read_fn);
        assert!(cond_input.output().influences_ctrl(&read.input()));
        assert!(other_cond.output().influences_ctrl(&read.input()));
        // SOUNDNESS: Need to target the output here, because this function takes no arguments.
        assert!(cond_input.output().influences_ctrl(&other_cond.output()));
        // The finer grained SPDG no longer has these as neighbors
        // assert!(cond_input.output().is_neighbor_ctrl(&other_cond.output()));
        assert!(other_cond.output().influences_next_control(&read.input()));
        assert!(!cond_input.output().influences_next_control(&read.input()));
    });
}
