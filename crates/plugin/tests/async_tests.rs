#![feature(rustc_private)]

use paralegal_flow::inline_test;
use paralegal_flow::test_utils::*;
use paralegal_pdg::CallString;
use paralegal_pdg::Identifier;
use std::sync::OnceLock;

const EXTRA_ARGS: [&str; 2] = ["--include=crate", "--no-adaptive-approximation"];

fn async_test_env() -> &'static DependencyEnvironment {
    static ENV: OnceLock<DependencyEnvironment> = OnceLock::new();
    ENV.get_or_init(|| {
        DependencyEnvironmentBuilder::new()
            .with_manifest("tests/async-tests/Cargo.toml")
            .build()
    })
}

#[test]
fn top_level_inlining_happens() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(noinline, return)]
        fn dp_user_data(user_data: &mut UserData) {}

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(user_data: &UserData) {}

        async fn main() {
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
        // This used to check for neighbors. But now "input" is not actually nodes
        // at the same location as the call site but one ahead, so the gap shortened.
        assert!(!get.output().overlaps(&send.input()))
    });
}

#[test]
fn awaiting_works() {
    inline_test! {

        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source)]
        async fn async_get_user_data() -> UserData {
            return UserData {
                data: vec![1, 2, 3],
            };
        }

        #[paralegal_flow::marker(
            yey_paralegal_flow_now_needs_this_label_or_it_will_recurse_into_this_function,
            return
        )]
        async fn async_dp_user_data(user_data: &mut UserData) {
            for i in &mut user_data.data {
                *i = 2;
            }
        }
        #[paralegal_flow::marker{ sink, arguments = [0] }]
        async fn async_send_user_data(user_data: &UserData) {}


        async fn main() {
            let mut user_data = async_get_user_data().await;
            async_dp_user_data(&mut user_data).await;
            async_send_user_data(&user_data).await;
        }
    }
    .check_ctrl(|graph| {
        let get_fn = graph.async_function("async_get_user_data");
        let get = graph.call_site(&get_fn);
        let dp_fn = graph.async_function("async_dp_user_data");
        let dp = graph.call_site(&dp_fn);
        let send_fn = graph.async_function("async_send_user_data");
        let send = graph.call_site(&send_fn);

        assert!(get.output().flows_to_data(&dp.input()));
        assert!(dp.output().flows_to_data(&send.input()));
        assert!(get.output().flows_to_data(&send.input()));
        assert!(!get.output().is_neighbor_data(&send.input()))
    });
}

#[test]
fn two_data_over_boundary() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data2() -> UserData { UserData { data: vec![4, 5, 6] } }

        #[paralegal_flow::marker(source, return)]
        async fn async_get_user_data() -> UserData { UserData { data: vec![7, 8, 9] } }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(user_data: &UserData) {}

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data2(user_data: &UserData) {}

        async fn main() {
            let user_data1 = get_user_data();
            let user_data2 = get_user_data2();
            let _ = async_get_user_data().await;
            send_user_data(&user_data1);
            send_user_data2(&user_data2);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let get2_fn = graph.function("get_user_data2");
        let get2 = graph.call_site(&get2_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);
        let send2_fn = graph.function("send_user_data2");
        let send2 = graph.call_site(&send2_fn);

        assert!(get.output().flows_to_data(&send.input()));
        assert!(get2.output().flows_to_data(&send2.input()));
        assert!(!get.output().flows_to_data(&send2.input()));
        assert!(!get2.output().flows_to_data(&send.input()));
    });
}

#[test]
#[ignore = "Odd aliasing behavior with async. See https://github.com/brownsys/paralegal/issues/144"]
fn inlining_crate_local_async_fns() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        async fn inlineable_async_dp_user_data(user_data: &mut UserData) {
            dp_user_data(user_data)
        }

        #[paralegal_flow::marker{ sink, arguments = [0] }]
        fn send_user_data(user_data: &UserData) {}

        #[paralegal_flow::marker(source)]
        fn get_user_data() -> UserData {
            return UserData {
                data: vec![1, 2, 3],
            };
        }
        #[paralegal_flow::marker(
            yey_paralegal_flow_now_needs_this_label_or_it_will_recurse_into_this_function,
            return
        )]
        fn dp_user_data(user_data: &mut UserData) {
            for i in &mut user_data.data {
                *i = 2;
            }
        }

        async fn main() {
            let mut user_data = get_user_data();
            inlineable_async_dp_user_data(&mut user_data).await;
            send_user_data(&user_data);
        }
    }
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
        assert!(!get.output().is_neighbor_data(&send.input()))
    });
}

// define_test!(arguments_work skip
//     "arguments are not emitted properly in the graph data structure the test is defined over, making the test fail. When I manually inspected the (visual) graph dump this test case seemed to be correct." : graph -> {
//     let send_fn = graph.function("send_user_data");
//     let send = graph.call_site(&send_fn);
//     let data = graph.argument(graph.ctrl(), 0);
//     assert!(graph.connects_data((data, send.1), send));
// });

#[test]
#[ignore = "Alias analysis is problematic with async.
    See https://github.com/willcrichton/flowistry/issues/93"]
fn no_inlining_overtaint() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source)]
        fn get_user_data() -> UserData {
            return UserData {
                data: vec![1, 2, 3],
            };
        }

        #[paralegal_flow::marker(source)]
        fn get_user_data2() -> UserData {
            return UserData {
                data: vec![1, 2, 3],
            };
        }

        #[paralegal_flow::marker(
            yey_paralegal_flow_now_needs_this_label_or_it_will_recurse_into_this_function,
            return
        )]
        fn dp_user_data(user_data: &mut UserData) {
            for i in &mut user_data.data {
                *i = 2;
            }
        }

        async fn arity2_inlineable_async_dp_user_data(_: &mut UserData, user_data: &mut UserData) {
            dp_user_data(user_data)
        }

        #[paralegal_flow::marker{ sink, arguments = [0] }]
        fn send_user_data(user_data: &UserData) {}

        #[paralegal_flow::marker{ sink, arguments = [0] }]
        fn send_user_data2(user_data: &UserData) {}

        async fn main() {
            let mut ud1 = get_user_data();
            let mut ud2 = get_user_data2();
            arity2_inlineable_async_dp_user_data(&mut ud1, &mut ud2).await;
            send_user_data(&ud1);
            send_user_data2(&ud2);
        }
    }
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let get2_fn = graph.function("get_user_data2");
        let get2 = graph.call_site(&get2_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);
        let send2_fn = graph.function("send_user_data2");
        let send2 = graph.call_site(&send2_fn);
        let dp_fn = graph.function("dp_user_data");
        let dp = graph.call_site(&dp_fn);

        assert!(get.output().flows_to_data(&send.input()));
        assert!(get2.output().flows_to_data(&send2.input()));
        assert!(get2.output().flows_to_data(&dp.input()));
        assert!(!get.output().flows_to_data(&dp.input()));

        assert!(!get.output().flows_to_data(&send2.input()));
        assert!(!get2.output().flows_to_data(&send.input()));
    });
}

#[test]
#[ignore = "Odd aliasing behavior with async. See https://github.com/brownsys/paralegal/issues/144"]
fn no_immutable_inlining_overtaint() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source)]
        fn get_user_data() -> UserData {
            return UserData {
                data: vec![1, 2, 3],
            };
        }

        #[paralegal_flow::marker(source)]
        fn get_user_data2() -> UserData {
            return UserData {
                data: vec![1, 2, 3],
            };
        }

        #[paralegal_flow::marker{ sink, arguments = [0] }]
        fn send_user_data(user_data: &UserData) {}

        #[paralegal_flow::marker{ sink, arguments = [0] }]
        fn send_user_data2(user_data: &UserData) {}

        async fn send_both(ud1: &UserData, ud2: &UserData) {
            send_user_data(&ud1);
            send_user_data2(&ud2);
        }

        async fn main() {
            let mut ud1 = get_user_data();
            let mut ud2 = get_user_data2();
            send_both(&ud1, &ud2).await;
        }
    }
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let get2_fn = graph.function("get_user_data2");
        let get2 = graph.call_site(&get2_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);
        let send2_fn = graph.function("send_user_data2");
        let send2 = graph.call_site(&send2_fn);

        assert!(get.output().flows_to_data(&send.input()));
        assert!(get2.output().flows_to_data(&send2.input()));
        assert!(!get.output().flows_to_data(&send2.input()));
        assert!(!get2.output().flows_to_data(&send.input()));
    });
}

#[test]
fn no_mixed_mutability_borrow_inlining_overtaint() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source)]
        fn get_user_data() -> UserData {
            return UserData {
                data: vec![1, 2, 3],
            };
        }

        #[paralegal_flow::marker(source)]
        fn get_user_data2() -> UserData {
            return UserData {
                data: vec![1, 2, 3],
            };
        }

        #[paralegal_flow::marker(
            yey_paralegal_flow_now_needs_this_label_or_it_will_recurse_into_this_function,
            return
        )]
        fn dp_user_data(user_data: &mut UserData) {
            for i in &mut user_data.data {
                *i = 2;
            }
        }

        async fn arity2_inlineable_async_dp_user_data2(_: &UserData, user_data: &mut UserData) {
            dp_user_data(user_data)
        }

        #[paralegal_flow::marker{ sink, arguments = [0] }]
        fn send_user_data(user_data: &UserData) {}

        #[paralegal_flow::marker{ sink, arguments = [0] }]
        fn send_user_data2(user_data: &UserData) {}

        async fn main() {
            let mut ud1 = get_user_data();
            let mut ud2 = get_user_data2();
            arity2_inlineable_async_dp_user_data2(&ud1, &mut ud2).await;
            send_user_data(&ud1);
            send_user_data2(&ud2);
        }
    }
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let get2_fn = graph.function("get_user_data2");
        let get2 = graph.call_site(&get2_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);
        let send2_fn = graph.function("send_user_data2");
        let send2 = graph.call_site(&send2_fn);

        assert!(get.output().flows_to_data(&send.input()));
        assert!(get2.output().flows_to_data(&send2.input()));
        assert!(!get2.output().flows_to_data(&send.input()));
        assert!(!get.output().flows_to_data(&send2.input()));
    });
}

#[test]
#[ignore = "Alias analysis is problematic with async.
    See https://github.com/willcrichton/flowistry/issues/93"]
fn no_mixed_mutability_inlining_overtaint() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source)]
        fn get_user_data() -> UserData {
            return UserData {
                data: vec![1, 2, 3],
            };
        }

        #[paralegal_flow::marker(source)]
        fn get_user_data2() -> UserData {
            return UserData {
                data: vec![1, 2, 3],
            };
        }

        #[paralegal_flow::marker{ sink, arguments = [0] }]
        fn send_user_data(user_data: &UserData) {}

        #[paralegal_flow::marker{ sink, arguments = [0] }]
        fn send_user_data2(user_data: &UserData) {}

        async fn send_both2(ud1: &UserData, ud2: &mut UserData) {
            send_user_data(&ud1);
            send_user_data2(&ud2);
        }

        async fn main() {
            let mut ud1 = get_user_data();
            let mut ud2 = get_user_data2();
            send_both2(&ud1, &mut ud2).await;
        }
    }
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let get2_fn = graph.function("get_user_data2");
        let get2 = graph.call_site(&get2_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);
        let send2_fn = graph.function("send_user_data2");
        let send2 = graph.call_site(&send2_fn);

        assert!(get.output().flows_to_data(&send.input()));
        assert!(get2.output().flows_to_data(&send2.input()));
        assert!(!get2.output().flows_to_data(&send.input()));
        assert!(!get.output().flows_to_data(&send2.input()));
    });
}

#[test]
fn no_value_inlining_overtaint() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data2() -> UserData { UserData { data: vec![4, 5, 6] } }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(user_data: &UserData) {}

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data2(user_data: &UserData) {}

        async fn move_send_both(ud1: UserData, ud2: UserData) {
            send_user_data(&ud1);
            send_user_data2(&ud2);
        }

        async fn main() {
            let ud1 = get_user_data();
            let ud2 = get_user_data2();
            move_send_both(ud1, ud2).await;
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let get2_fn = graph.function("get_user_data2");
        let get2 = graph.call_site(&get2_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);
        let send2_fn = graph.function("send_user_data2");
        let send2 = graph.call_site(&send2_fn);

        assert!(get.output().flows_to_data(&send.input()));
        assert!(get2.output().flows_to_data(&send2.input()));
        assert!(!get.output().flows_to_data(&send2.input()));
        assert!(!get2.output().flows_to_data(&send.input()));
    });
}

#[test]
#[ignore = "We no longer remove the state machine. I preserve this test case
    if we want to do that removal in the future."]
fn remove_poll_match() {
    inline_test! {
        #[paralegal_flow::marker(noinline)]
        async fn f() -> usize {
            0
        }

        #[paralegal_flow::marker(noinline)]
        fn some_input() -> usize {
            0
        }

        #[paralegal_flow::marker(target)]
        fn target(i: usize) {}

        async fn main() {
            let p = some_input();
            let x = f().await;
            let y = target(p);
            ()
        }
    }
    .check_ctrl(|graph| {
        let input_fn = graph.function("some_input");
        let input = graph.call_site(&input_fn);
        let target_fn = graph.function("target");
        let target = graph.call_site(&target_fn);
        let poll_fn = graph.function("poll");
        let poll = graph.call_site(&poll_fn);
        let new_unchecked_fn = graph.function("new_unchecked");
        let new_unchecked = graph.call_site(&new_unchecked_fn);
        let get_context_fn = graph.function("get_context");
        let get_context = graph.call_site(&get_context_fn);
        let into_future_fn = graph.function("into_future");
        let into_future = graph.call_site(&into_future_fn);
        let _f_fn = graph.function("f");
        let _f = graph.call_site(&_f_fn);
        assert!(input.output().flows_to_data(&target.input()));

        assert!(poll.output().is_terminal());
        assert!(new_unchecked.output().is_terminal());
        assert!(get_context.output().is_terminal());
        assert!(into_future.output().is_terminal());
    });
}

#[test]
fn no_overtaint_over_poll() {
    inline_test! {
        #[paralegal_flow::marker(noinline)]
        async fn f() -> usize {
            0
        }

        #[paralegal_flow::marker(noinline)]
        fn some_input() -> usize {
            0
        }

        #[paralegal_flow::marker(noinline)]
        fn another_input() -> usize {
            9
        }

        #[paralegal_flow::marker(target)]
        fn target(i: usize) {}

        #[paralegal_flow::marker(target)]
        fn another_target(i: usize) {}

        async fn id_fun<T>(t: T) -> T {
            let _ = f();
            t
        }

        async fn main() {
            let p = some_input();
            let q = another_input();
            let t = id_fun((p, q)).await;
            target(t.0);
            another_target(t.1);
        }
    }
    .check_ctrl(|graph| {
        let input_fn = graph.function("some_input");
        let input = graph.call_site(&input_fn);
        let another_input_fn = graph.function("another_input");
        let another_input = graph.call_site(&another_input_fn);

        let target_fn = graph.function("target");
        let target = graph.call_site(&target_fn);
        let another_target_fn = graph.function("another_target");
        let another_target = graph.call_site(&another_target_fn);

        assert!(input.output().flows_to_data(&target.input()));
        assert!(
            another_input
                .output()
                .flows_to_data(&another_target.input())
        );
        assert!(!dbg!(input.output()).flows_to_data(&dbg!(another_target.input())));
        assert!(!another_input.output().flows_to_data(&target.input()));
    });
}

#[test]
fn return_from_async() {
    inline_test! {
        #[paralegal_flow::marker(noinline, return)]
        fn some_input() -> usize { 0 }

        async fn main() -> usize {
            some_input()
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let input_fn = graph.function("some_input");
        let instruction_info = &graph.graph().desc.instruction_info;
        println!("Looking for function {:?}", input_fn.ident);
        let filter = |m: CallString| {
            instruction_info[&m.leaf()]
                .kind
                .as_function_call()
                .is_some_and(|i| i.id == input_fn.ident)
        };
        for e in graph.spdg().graph.edge_weights().filter(|e| filter(e.at)) {
            println!("Edge {e} is at function in question");
        }
        for n in graph.spdg().graph.node_weights().filter(|n| filter(n.at)) {
            println!("Node {n} is at function in question");
        }
        let input = graph.call_site(&input_fn);

        assert!(graph.returns(&input.output()))
    });
}

#[test]
fn async_return_from_async() {
    inline_test! {
        #[paralegal_flow::marker(noinline)]
        async fn f() -> usize { 0 }

        #[paralegal_flow::marker(noinline, return)]
        fn some_input() -> usize { 0 }

        async fn id_fun<T>(t: T) -> T {
            let _ = f();
            t
        }

        async fn main() -> usize {
            id_fun(some_input()).await
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let input_fn = graph.function("some_input");
        let input = graph.call_site(&input_fn);
        dbg!(graph.return_value());
        assert!(graph.returns(&dbg!(input.output())))
    });
}

#[test]
fn markers() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        async fn src() -> usize { 0 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        async fn snk(snk: usize) {}

        async fn main() {
            snk(src().await).await
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let input = graph.marked(Identifier::new_intern("source"));
        let output = graph.marked(Identifier::new_intern("sink"));

        assert!(!input.is_empty());
        assert!(!output.is_empty());
        assert!(input.flows_to_data(&output));
    });
}

#[test]
fn await_on_generic() {
    InlineTestBuilder::new(stringify!(
        use std::{
            future::{Future},
            task::{Context, Poll},
            pin::Pin
        };
        struct AFuture;

        impl Future for AFuture {
            type Output = usize;
            fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                unimplemented!()
            }
        }

        trait Trait {
            fn method(&mut self) -> AFuture;
        }

        async fn main<T: Trait>(mut t: T) -> usize {
            t.method().await
        }
    ))
    .check_ctrl(|_ctrl| {})
}
#[test]
fn await_with_inner_generic_sanity() {
    InlineTestBuilder::new(stringify!(
        use std::{
            future::{Future},
            task::{Context, Poll},
            pin::Pin,
        };
        struct AFuture<'a, T: ?Sized>(&'a mut T);

        impl<'a, T> Future for AFuture<'a, T> {
            type Output = usize;
            fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                unimplemented!()
            }
        }

        trait Trait {
            fn method(&mut self) -> AFuture<'_, Self> {
                AFuture(self)
            }
        }

        struct Impl;

        impl Trait for Impl {}

        async fn main(mut t: Impl) -> usize {
            t.method().await
        }
    ))
    .check_ctrl(|_ctrl| {})
}

#[test]
fn await_with_inner_generic() {
    InlineTestBuilder::new(stringify!(
        use std::{
            future::{Future},
            task::{Context, Poll},
            pin::Pin,
        };
        struct AFuture<'a, T: ?Sized>(&'a mut T);

        impl<'a, T: ?Sized> Future for AFuture<'a, T> {
            type Output = usize;
            fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                unimplemented!()
            }
        }

        trait Trait {
            fn method(&mut self) -> AFuture<'_, Self> {
                AFuture(self)
            }
        }

        async fn main<T: Trait>(mut t: T) -> usize {
            t.method().await
        }
    ))
    .check_ctrl(|_ctrl| {})
}

#[test]
fn await_with_inner_generic_constrained() {
    InlineTestBuilder::new(stringify!(
        use std::{
            future::{Future},
            task::{Context, Poll},
            pin::Pin,
        };
        struct AFuture<'a, T: ?Sized>(&'a mut T);

        impl<'a, T: Trait + Unpin + ?Sized> Future for AFuture<'a, T> {
            type Output = usize;
            fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                unimplemented!()
            }
        }

        trait Trait: Send + Unpin + 'static {
            fn method(&mut self) -> AFuture<'_, Self>
            where
                Self: Unpin + Sized,
            {
                AFuture(self)
            }
        }

        async fn main<T: Trait>(mut t: T) -> usize {
            t.method().await
        }
    ))
    .check_ctrl(|_ctrl| {})
}

#[test]
fn async_through_another_layer() {
    InlineTestBuilder::new(stringify!(
        async fn maker(x: u32, y: u32) -> u32 {
            x
        }

        fn get_async(x: u32, y: u32) -> impl std::future::Future<Output = u32> {
            maker(y, x)
        }

        #[paralegal_flow::marker(source, return)]
        fn mark_source<T>(t: T) -> T {
            t
        }

        #[paralegal_flow::marker(source_2, return)]
        fn mark_source_2<T>(t: T) -> T {
            t
        }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn sink<T>(t: T) {}

        async fn main() {
            let src = mark_source(1);
            let src2 = mark_source_2(2);
            sink(get_async(src, src2).await)
        }
    ))
    .with_extra_args(["--no-adaptive-approximation".to_string()])
    .check_ctrl(|ctrl| {
        let sources = ctrl.marked(Identifier::new_intern("source"));
        let source_2 = ctrl.marked(Identifier::new_intern("source_2"));
        let sinks = ctrl.marked(Identifier::new_intern("sink"));
        assert!(!sources.is_empty());
        assert!(!source_2.is_empty());
        assert!(!sinks.is_empty());
        assert!(!sources.flows_to_any(&sinks));
        assert!(source_2.flows_to_any(&sinks));
    })
}

#[test]
#[ignore = "https://github.com/brownsys/paralegal/issues/138"]
fn field_precision_at_future_creation() {
    InlineTestBuilder::new(stringify!(
        use std::{
            future::Future,
            task::{Context, Poll},
            pin::Pin,
        };

        struct MyFuture(u32);

        impl MyFuture {
            fn new(x: u32, y: u32) -> Self {
                MyFuture(x)
            }
        }

        impl Future for MyFuture {
            type Output = u32;
            fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                Poll::Ready(self.0)
            }
        }

        #[paralegal_flow::marker(source, return)]
        fn mark_source<T>(t: T) -> T {
            t
        }

        #[paralegal_flow::marker(source_2, return)]
        fn mark_source_2<T>(t: T) -> T {
            t
        }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn sink<T>(t: T) {}

        async fn main() {
            let src = mark_source(1);
            let src2 = mark_source_2(2);
            sink(MyFuture::new(src, src2).await)
        }

    ))
    .check_ctrl(|ctrl| {
        let captured = ctrl.marked(Identifier::new_intern("source"));
        let dropped = ctrl.marked(Identifier::new_intern("source_2"));
        let sink = ctrl.marked(Identifier::new_intern("sink"));
        assert!(!captured.is_empty());
        assert!(!dropped.is_empty());
        assert!(captured.flows_to_any(&sink));
        assert!(!dropped.flows_to_any(&sink));
    })
}

#[test]
fn field_precision_at_future_consumption() {
    InlineTestBuilder::new(stringify!(
        use std::{
            future::Future,
            task::{Context, Poll},
            pin::Pin,
        };

        struct MyFuture(u32, u32);

        impl MyFuture {
            fn new(x: u32, y: u32) -> Self {
                MyFuture(x, y)
            }
        }

        impl Future for MyFuture {
            type Output = u32;
            fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                Poll::Ready(self.0)
            }
        }

        #[paralegal_flow::marker(source, return)]
        fn mark_source<T>(t: T) -> T {
            t
        }

        #[paralegal_flow::marker(source_2, return)]
        fn mark_source_2<T>(t: T) -> T {
            t
        }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn sink<T>(t: T) {}

        async fn main() {
            let src = mark_source(1);
            let src2 = mark_source_2(2);
            sink(MyFuture::new(src, src2).await)
        }

    ))
    .check_ctrl(|ctrl| {
        let sources = ctrl.marked(Identifier::new_intern("source"));
        let sinks = ctrl.marked(Identifier::new_intern("source_2"));
        assert!(!sources.is_empty());
        assert!(!sinks.is_empty());
        // Ignored until https://github.com/brownsys/paralegal/issues/138 is fixed
        // assert!(!sources.flows_to_any(&ctrl.marked(Identifier::new_intern("sink"))));
        // assert!(sinks.flows_to_any(&ctrl.marked(Identifier::new_intern("sink"))));
    })
}

fn control_flow_overtaint_check(ctrl: CtrlRef<'_>) {
    let checks = ctrl.marked(Identifier::new_intern("is_check"));
    let sensitive_1 = dbg!(ctrl.marked(Identifier::new_intern("is_sensitive1")));
    let sensitive_2 = dbg!(ctrl.marked(Identifier::new_intern("is_sensitive2")));

    assert!(!checks.is_empty());
    assert!(!sensitive_1.is_empty());
    assert!(!sensitive_2.is_empty());

    assert!(checks.influences_ctrl(&sensitive_1));
    assert!(!checks.influences_ctrl(&sensitive_2));
}

#[test]
fn control_flow_overtaint() {
    InlineTestBuilder::new(stringify!(
        #[paralegal_flow::marker(is_check, return)]
        async fn perform_check(data: usize) -> Result<(), ()> {
            if data != 0 { Ok(()) } else { Err(()) }
        }

        #[paralegal_flow::marker(is_sensitive1, return)]
        async fn sensitive_action1(data: usize) {}

        #[paralegal_flow::marker(is_sensitive2, return)]
        async fn sensitive_action2(data: usize) {}

        async fn main(condition: bool, data: usize) -> Result<(), ()> {
            if condition {
                perform_check(data).await?;

                sensitive_action1(data).await;
            } else {
                sensitive_action2(data).await;
            }
            Ok(())
        }
    ))
    .check_ctrl(control_flow_overtaint_check);
}

#[test]
fn control_flow_overtaint_tracing() {
    inline_test! {
        use tracing;

        #[paralegal_flow::marker(is_check, return)]
        async fn perform_check(data: usize) -> Result<(), ()> {
            if data != 0 { Ok(()) } else { Err(()) }
        }

        #[paralegal_flow::marker(is_sensitive1, return)]
        async fn sensitive_action1(data: usize) {}

        #[paralegal_flow::marker(is_sensitive2, return)]
        async fn sensitive_action2(data: usize) {}

        #[tracing::instrument(skip_all)]
        async fn main(condition: bool, data: usize) -> Result<(), ()> {
            if condition {
                perform_check(data).await?;
                sensitive_action1(data).await;
            } else {
                sensitive_action2(data).await;
            }
            Ok(())
        }
    }
    .with_dependency_environment(async_test_env())
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(control_flow_overtaint_check);
}

#[test]
fn control_flow_overtaint_tracing_unasync() {
    inline_test! {
        use tracing;

        #[paralegal_flow::marker(is_check, return)]
        fn perform_check(data: usize) -> Result<(), ()> {
            if data != 0 { Ok(()) } else { Err(()) }
        }

        #[paralegal_flow::marker(is_sensitive1, return)]
        fn sensitive_action1(data: usize) {}

        #[paralegal_flow::marker(is_sensitive2, return)]
        fn sensitive_action2(data: usize) {}

        #[tracing::instrument(skip_all)]
        fn main(condition: bool, data: usize) -> Result<(), ()> {
            if condition {
                perform_check(data)?;
                sensitive_action1(data);
            } else {
                sensitive_action2(data);
            }
            Ok(())
        }
    }
    .with_dependency_environment(async_test_env())
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(control_flow_overtaint_check);
}

#[test]
fn control_flow_overtaint_async_trait() {
    inline_test! {
        use async_trait::async_trait;

        #[paralegal_flow::marker(is_check, return)]
        async fn perform_check(data: usize) -> Result<(), ()> {
            if data != 0 { Ok(()) } else { Err(()) }
        }

        #[paralegal_flow::marker(is_sensitive1, return)]
        async fn sensitive_action1(data: usize) {}

        #[paralegal_flow::marker(is_sensitive2, return)]
        async fn sensitive_action2(data: usize) {}

        #[async_trait]
        trait MyAsyncTrait {
            async fn control_flow_overtaint_async_trait(&self, condition: bool, data: usize) -> Result<(), ()>;
        }

        struct Impl;

        #[async_trait]
        impl MyAsyncTrait for Impl {
            #[paralegal_flow::analyze]
            async fn control_flow_overtaint_async_trait(&self, condition: bool, data: usize) -> Result<(), ()> {
                if condition {
                    perform_check(data).await?;
                    sensitive_action1(data).await;
                } else {
                    sensitive_action2(data).await;
                }
                Ok(())
            }
        }
    }
    .with_dependency_environment(async_test_env())
    .with_extra_args(EXTRA_ARGS)
    .with_entrypoint("control_flow_overtaint_async_trait")
    .check_ctrl(control_flow_overtaint_check);
}

#[test]
fn control_flow_overtaint_async_trait_tracing() {
    inline_test! {
        use async_trait::async_trait;
        use tracing;

        #[paralegal_flow::marker(is_check, return)]
        async fn perform_check(data: usize) -> Result<(), ()> {
            if data != 0 { Ok(()) } else { Err(()) }
        }

        #[paralegal_flow::marker(is_sensitive1, return)]
        async fn sensitive_action1(data: usize) {}

        #[paralegal_flow::marker(is_sensitive2, return)]
        async fn sensitive_action2(data: usize) {}

        #[async_trait]
        trait MyAsyncTrait {
            async fn control_flow_overtaint_async_trait_tracing(&self, condition: bool, data: usize) -> Result<(), ()>;
        }

        struct Impl;

        #[async_trait]
        impl MyAsyncTrait for Impl {
            #[paralegal_flow::analyze]
            #[tracing::instrument(skip_all)]
            async fn control_flow_overtaint_async_trait_tracing(&self, condition: bool, data: usize) -> Result<(), ()> {
                if condition {
                    perform_check(data).await?;
                    sensitive_action1(data).await;
                } else {
                    sensitive_action2(data).await;
                }
                Ok(())
            }
        }
    }
    .with_dependency_environment(async_test_env())
    .with_extra_args(EXTRA_ARGS)
    .with_entrypoint("control_flow_overtaint_async_trait_tracing")
    .check_ctrl(control_flow_overtaint_check);
}

// Regression: a non-async trait method whose declared return type is
// `Pin<Box<dyn Future>>` but whose body just forwards a future from another
// call (no top-level `async {}` block) used to trip
// `find_coroutine_assign`'s `assert_eq!(len, 1)` because the signature
// satisfies `has_async_trait_signature` / `has_async_tool_signature`. This is
// exactly the shape of `reqwest_middleware::Middleware::handle` reached
// transitively from lemmy.
#[test]
fn pin_box_dyn_future_forwarder_does_not_panic() {
    inline_test! {
        use std::future::Future;
        use std::pin::Pin;

        #[paralegal_flow::marker(make_marker, return)]
        fn make_future() -> Pin<Box<dyn Future<Output = usize> + 'static>> {
            Box::pin(async { 42 })
        }

        trait Forwarder {
            fn forward(&self) -> Pin<Box<dyn Future<Output = usize> + 'static>>;
        }

        struct Impl;

        impl Forwarder for Impl {
            fn forward(&self) -> Pin<Box<dyn Future<Output = usize> + 'static>> {
                make_future()
            }
        }

        async fn main() {
            let i = Impl;
            let _ = i.forward().await;
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|_| ());
}

#[test]
fn explicit_call_to_poll() {
    InlineTestBuilder::new(stringify!(
        #![feature(noop_waker)]
        use std::pin::{Pin, pin};
        use std::future::Future;

        fn main() {
            let data1 = (1, 2,3, 4, 5);
            let data2 = (1, 2,3, 4, 5);
            let data3 = (1, 2,3, 4, 5);
            let mut f = pin!(async { println!("{}", data3.4); data1.4 + data2.4 });
            let waker = std::task::Waker::noop();
            let mut cx = std::task::Context::from_waker(&waker);
            let _ = f.as_mut().poll(&mut cx);
        }
    ))
    .with_extra_args([
        "--no-adaptive-approximation".to_string(),
        "--dump".to_string(),
        "spdg".to_string(),
        "--dump".to_string(),
        "mir".to_string(),
    ])
    .check_ctrl(|_| ());
}

#[test]
fn async_arg_markers() {
    inline_test! {
        #[paralegal_flow::marker(source, arguments = [0])]
        #[paralegal_flow::marker(no_source, arguments = [1])]
        #[paralegal_flow::marker(source_2, arguments = [2])]
        #[paralegal_flow::marker(sink, return)]
        async fn main(src: usize, other: usize, last: usize) -> usize {
            let some = src + other;
            src + 9 + last
        }
    }
    .check_ctrl(|ctrl| {
        // check direct
        let args = ctrl.arguments().as_singles().collect::<Vec<_>>();
        let [src, other, last] = args.as_slice() else {
            panic!("Expected exactly two arguments, got {:?}", args);
        };
        let returns = ctrl.return_value().as_singles().collect::<Vec<_>>();
        let [snk] = returns.as_slice() else {
            panic!("Expected exactly one return value, got {:?}", returns);
        };

        assert!(src.flows_to_data(snk));
        assert!(!other.flows_to_data(snk));
        assert!(last.flows_to_data(snk));

        // Check via markers
        let sources = ctrl.marked(Identifier::new_intern("source"));
        let source_2 = ctrl.marked(Identifier::new_intern("source_2"));
        let no_source = ctrl.marked(Identifier::new_intern("no_source"));
        let sinks = ctrl.marked(Identifier::new_intern("sink"));
        assert!(!sources.is_empty());
        assert!(!source_2.is_empty());
        assert!(!no_source.is_empty());
        assert!(!sinks.is_empty());
        assert!(sources.flows_to_any(&sinks));
        assert!(source_2.flows_to_any(&sinks));
        assert!(!no_source.flows_to_any(&sinks));
    })
}

// TODO marked type as argument test
#[test]
fn async_arg_marked_via_type() {
    inline_test! {
        #[paralegal_flow::marker(source)]
        struct T1(u32);

        #[paralegal_flow::marker(source_2)]
        struct T2(u32);

        #[paralegal_flow::marker(sink)]
        struct T3(u32);

        async fn main(src: T1, other: T2) -> T3 {
            let some = src.0 + other.0;
            T3(src.0 + 9)
        }
    }
    .check_ctrl(|ctrl| {
        let sources = ctrl.marked(Identifier::new_intern("source"));
        let source_2 = ctrl.marked(Identifier::new_intern("source_2"));
        let sinks = ctrl.marked(Identifier::new_intern("sink"));
        assert!(!sources.is_empty());
        assert!(!source_2.is_empty());
        assert!(!sinks.is_empty());
        assert!(sources.flows_to_any(&sinks));
        assert!(!source_2.flows_to_any(&sinks));
    })
}

#[test]
fn async_args_and_local_variable() {
    inline_test! {
        #[paralegal_flow::marker(noinline, return)]
        async fn i_force_await() {

        }

        fn compute() -> usize {
            42
        }

        #[paralegal_flow::marker(source, arguments = [0])]
        #[paralegal_flow::marker(no_source, arguments = [1])]
        #[paralegal_flow::marker(source_2, arguments = [2])]
        #[paralegal_flow::marker(sink, return)]
        async fn main(src: usize, other: usize, last: usize) -> usize {
            let some = src + other;
            let intermediate = last + compute();
            i_force_await().await;
            src + intermediate
        }
    }
    .check_ctrl(|ctrl| {
        // Check via markers
        let sources = ctrl.marked(Identifier::new_intern("source"));
        let source_2 = ctrl.marked(Identifier::new_intern("source_2"));
        let no_source = ctrl.marked(Identifier::new_intern("no_source"));
        let sinks = ctrl.marked(Identifier::new_intern("sink"));
        assert!(!sources.is_empty());
        assert!(!source_2.is_empty());
        assert!(!no_source.is_empty());
        assert!(!sinks.is_empty());
        assert!(sources.flows_to_any(&sinks));
        assert!(source_2.flows_to_any(&sinks));
        assert!(!no_source.flows_to_any(&sinks));
    })
}

#[test]
fn pattern_arguments() {
    inline_test! {
        struct Params {
            one: usize,
            two: usize,
            three: usize,
            four: usize,
        }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn marked(result: usize) {
            assert_eq!(result, 42);
        }

        #[paralegal_flow::marker(source, arguments = [0])]
        async fn main(Params { one, two, three, four } : Params) {
            let result = one + three + four;
            marked(result);
        }
    }
    .check_ctrl(|ctrl| {
        let target = ctrl.marked(Identifier::new_intern("target"));
        let source = ctrl.marked(Identifier::new_intern("source"));
        assert!(!target.is_empty());
        assert!(!source.is_empty());
        assert!(source.flows_to_data(&target));
    });
}

#[test]
fn pattern_arguments_poor_mans_tool_def() {
    inline_test! {
        struct Params {
            one: usize,
            two: usize,
            three: usize,
            four: usize,
        }

        #[paralegal_flow::marker(target, arguments = [0])]
        fn marked(result: usize) {
            assert_eq!(result, 42);
        }

        #[paralegal_flow::marker(source, arguments = [0])]
        fn main(Params { one, two, three, four } : Params)
            -> std::pin::Pin<std::boxed::Box<dyn std::future::Future<Output = ()>>> {
            std::boxed::Box::pin(async move {
                let result = one + three + four;
                marked(result);
            }) as std::pin::Pin<std::boxed::Box<dyn std::future::Future<Output = ()>>>
        }
    }
    .check_ctrl(|ctrl| {
        let target = ctrl.marked(Identifier::new_intern("target"));
        let source = ctrl.marked(Identifier::new_intern("source"));
        assert!(!target.is_empty());
        assert!(!source.is_empty());
        assert!(source.flows_to_data(&target));
    });
}

// Box-pattern (poor-man's tool def) where the captured upvar is derived from
// only one of several outer-fn args. Verifies that args not involved in the
// capture chain do NOT flow to a sink reachable through it.
//
// Currently fails: when the closure captures a non-arg local,
// `fix_async_args` conservatively wires every outer-fn arg to that env field,
// over-tainting unrelated args. Tightening this requires tracing the capture
// back through the outer body (e.g. via flowistry's local analysis on the
// outer body) to identify the actual arg dependencies.
#[test]
#[ignore = "fix_async_args over-approximates non-arg captures in box-pattern controllers"]
fn pattern_arguments_poor_mans_tool_def_arg_isolation() {
    inline_test! {
        #[paralegal_flow::marker(target, arguments = [0])]
        fn marked(result: usize) {
            assert_eq!(result, 42);
        }

        #[paralegal_flow::marker(source, arguments = [0])]
        #[paralegal_flow::marker(no_source, arguments = [1])]
        fn main(src: usize, other: usize)
            -> std::pin::Pin<std::boxed::Box<dyn std::future::Future<Output = ()>>> {
            // `derived` is a non-arg local, so the closure captures a non-arg
            // upvar — the case where `outer_args_for_capture` falls back from
            // direct-arg wiring.
            let derived = src + 1;
            let _ = other;
            std::boxed::Box::pin(async move {
                marked(derived);
            }) as std::pin::Pin<std::boxed::Box<dyn std::future::Future<Output = ()>>>
        }
    }
    .check_ctrl(|ctrl| {
        let target = ctrl.marked(Identifier::new_intern("target"));
        let source = ctrl.marked(Identifier::new_intern("source"));
        let no_source = ctrl.marked(Identifier::new_intern("no_source"));
        assert!(!target.is_empty());
        assert!(!source.is_empty());
        assert!(!no_source.is_empty());
        assert!(source.flows_to_data(&target));
        assert!(!no_source.flows_to_data(&target));
    });
}
