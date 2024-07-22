#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use paralegal_flow::test_utils::*;
use paralegal_spdg::Identifier;

const CRATE_DIR: &str = "tests/async-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump(CRATE_DIR);
}

macro_rules! define_test {
    ($($t:tt)*) => {
        paralegal_flow::define_flow_test_template!(TEST_CRATE_ANALYZED, CRATE_DIR, $($t)*);
    };
}

define_test!(top_level_inlining_happens : graph -> {
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

define_test!(awaiting_works : graph -> {
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

define_test!(two_data_over_boundary : graph -> {
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

define_test!(inlining_crate_local_async_fns
    skip
    "Odd aliasing behavior with async. See https://github.com/brownsys/paralegal/issues/144"
    : graph -> {

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

// define_test!(arguments_work skip
//     "arguments are not emitted properly in the graph data structure the test is defined over, making the test fail. When I manually inspected the (visual) graph dump this test case seemed to be correct." : graph -> {
//     let send_fn = graph.function("send_user_data");
//     let send = graph.call_site(&send_fn);
//     let data = graph.argument(graph.ctrl(), 0);
//     assert!(graph.connects_data((data, send.1), send));
// });

define_test!(no_inlining_overtaint
    skip
    "Alias analysis is problematic with async.
    See https://github.com/willcrichton/flowistry/issues/93"
    : graph -> {
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

define_test!(no_immutable_inlining_overtaint
    skip
    "Odd aliasing behavior with async. See https://github.com/brownsys/paralegal/issues/144"
    : graph -> {
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

define_test!(no_mixed_mutability_borrow_inlining_overtaint
    skip
    "Alias analysis is problematic with async.
    See https://github.com/willcrichton/flowistry/issues/93"
    : graph -> {
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

define_test!(no_mixed_mutability_inlining_overtaint
    skip
    "Alias analysis is problematic with async.
    See https://github.com/willcrichton/flowistry/issues/93"
    : graph -> {
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

define_test!(no_value_inlining_overtaint : graph -> {
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

define_test!(remove_poll_match
    skip
    "We no longer remove the state machine. I preserve this test case
    if we want to do that removal in the future."
    : graph -> {
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

define_test!(no_overtaint_over_poll
    skip
    "Field level precision across function calls is broken.
    See https://github.com/willcrichton/flowistry/issues/94."
    : graph -> {
    let input_fn = graph.function("some_input");
    let input = graph.call_site(&input_fn);
    let another_input_fn = graph.function("another_input");
    let another_input = graph.call_site(&another_input_fn);

    let target_fn = graph.function("target");
    let target = graph.call_site(&target_fn);
    let another_target_fn = graph.function("another_target");
    let another_target = graph.call_site(&another_target_fn);

    assert!(input.output().flows_to_data(&target.input()));
    assert!(another_input.output().flows_to_data(&another_target.input()));
    assert!(!dbg!(input.output()).flows_to_data(&dbg!(another_target.input())));
    assert!(!another_input.output().flows_to_data(&target.input()));
});

define_test!(return_from_async: graph -> {
    let input_fn = graph.function("some_input");
    let input = graph.call_site(&input_fn);

    assert!(graph.returns(&input.output()))
});

define_test!(async_return_from_async: graph -> {
    let input_fn = graph.function("some_input");
    let input = graph.call_site(&input_fn);
    dbg!(graph.return_value());
    assert!(graph.returns(&dbg!(input.output())))
});

define_test!(markers: graph -> {
    let input = graph.marked(Identifier::new_intern("source"));
    let output = graph.marked(Identifier::new_intern("sink"));

    assert!(!input.is_empty());
    assert!(!output.is_empty());
    assert!(input.flows_to_data(&output));
});

#[test]
fn selector_await_on_generic() {
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
    .check(|_ctrl| {})
}

#[test]
#[ignore = "https://github.com/brownsys/paralegal/issues/159"]
fn await_with_inner_generic() {
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

        async fn main<T: Trait>(mut t: T) -> usize {
            t.method().await
        }
    ))
    .check(|_ctrl| {})
}

#[test]
#[ignore = "https://github.com/brownsys/paralegal/issues/159"]
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
    .check(|_ctrl| {})
}

#[test]
fn selector_async_through_another_layer() {
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
    .check(|ctrl| {
        let sources = ctrl.marked(Identifier::new_intern("source"));
        let sinks = ctrl.marked(Identifier::new_intern("source_2"));
        assert!(!sources.is_empty());
        assert!(!sinks.is_empty());
        assert!(!sources.flows_to_any(&ctrl.marked(Identifier::new_intern("sink"))));
        assert!(sinks.flows_to_any(&ctrl.marked(Identifier::new_intern("sink"))));
    })
}
