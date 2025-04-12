#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use paralegal_flow::{define_flow_test_template, test_utils::*};

const CRATE_DIR: &str = "tests/new-alias-analysis-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool =
        run_paralegal_flow_with_flow_graph_dump_and(CRATE_DIR, ["--no-include-all"]);
}

macro_rules! define_test {
    ($($t:tt)*) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, CRATE_DIR, $($t)*);
    };
}

define_test!(track_mutable_modify : graph -> {
    let source_fn = graph.function("new_s");
    let source = graph.call_site(&source_fn);
    let modify_fn = graph.function("modify_it");
    let modify = graph.call_site(&modify_fn);
    let read_fn = graph.function("read");
    let read = graph.call_site(&read_fn);

    assert!(source.output().is_neighbor_data(&modify.input()));
    assert!(modify.output().is_neighbor_data(&read.input()));
    assert!(source.output().is_neighbor_data(&read.input()));
});

define_test!(eliminate_return_connection skip
    "Returning references has undecided PDG semantics. See\
    https://github.com/willcrichton/flowistry/issues/90" : graph -> {
    let source_fn = graph.function("new_s");
    let source = graph.call_site(&source_fn);
    let pass_through_fn = graph.function("deref_t");
    let pass_through = graph.call_site(&pass_through_fn);
    let read_fn = graph.function("read");
    let read = graph.call_site(&read_fn);

    assert!(dbg!(source.output()).always_happens_before_data(&dbg!(pass_through.output()), &dbg!(read.input())));
});

define_test!(eliminate_mut_input_connection: graph -> {
    let source_fn = graph.function("new_s");
    let source = graph.call_site(&source_fn);
    let push_fn = graph.function("push");
    let push = graph.call_site(&push_fn);
    let read_fn = graph.function("read");
    let read = graph.call_site(&read_fn);

    assert!(source.output().is_neighbor_data(&push.input()));
    assert!(push.output().is_neighbor_data(&read.input()));
});

define_test!(input_elimination_isnt_a_problem_empty
    skip
    "Alias analysis is  configured to abstract via lifetimes
    only at the moment. See https://github.com/willcrichton/flowistry/issues/93"
    : graph -> {
    let source_fn = graph.function("new_s");
    let source = graph.call_site(&source_fn);
    let read_fn = graph.function("read");
    let read = graph.call_site(&read_fn);

    assert!(!source.output().flows_to_data(&read.input()));
});

define_test!(input_elimination_isnt_a_problem_vec_push  : graph -> {
    // I don't remember how important it is for this test case that these test
    // "neighbor" relations but some of the assertions here are no longer a
    // neighbors. This is both because statements are now in the PDG and because
    // callees now have "start" and "end" locations.
    //
    // Basically everything that is "flows_to_data" here used to be
    // "is_neighbor_data".
    let source_fn = graph.function("new_s");
    let source = graph.call_site(&source_fn);
    let push_fn = graph.function("push");
    let push = graph.call_site(&push_fn);
    let insert_fn = graph.function("insert");
    let insert = graph.call_site(&insert_fn);
    let read_fn = graph.function("read");
    let read = graph.call_site(&read_fn);

    assert!(source.output().is_neighbor_data(&insert.input()));
    assert!(insert.output().flows_to_data(&push.input()));
    assert!(push.output().flows_to_data(&read.input()));
    assert!(source.output().flows_to_data(&push.input()));
    // This is where the overtaint happens
    assert!(insert.output().always_happens_before_data(&push.output(), &read.input()));

    // This is no longer true, because an additional direct edge is inserted
    // because the lifetimes guarantee that the source also reaches `read`
    // unmodified.
    // assert!(source.output().always_happens_before_data(&push.output(), &read.input()));
});

define_test!(input_elimination_isnt_a_problem_statement : graph -> {
    let src_1_fn = graph.function("new_s");
    let src_1 = graph.call_site(&src_1_fn);
    let src_2_fn = graph.function("another_s");
    let src_2 = graph.call_site(&src_2_fn);

    let assoc_fn = graph.function("assoc");
    let assoc = graph.call_site(&assoc_fn);

    let read_fn = graph.function("read");
    let read = graph.call_site(&read_fn);

    assert!(src_1.output().is_neighbor_data(&assoc.input()));
    assert!(assoc.output().is_neighbor_data(&read.input()));
    assert!(src_2.output().is_neighbor_data(&read.input()));

    // This is no longer true, because an additional direct edge is inserted
    // because the lifetimes guarantee that the source also reaches `read`
    // unmodified.
    // assert!(!src_1.output().is_neighbor_data(&read.input()));
});

define_test!(no_inlining_overtaint : graph -> {
    let get_fn = graph.function("get_user_data");
    let get = graph.call_site(&get_fn);
    let get2_fn = graph.function("get2_user_data");
    let get2 = graph.call_site(&get2_fn);
    let send_fn = graph.function("send_user_data");
    let send = graph.call_site(&send_fn);
    let send2_fn = graph.function("send2_user_data");
    let send2 = graph.call_site(&send2_fn);
    let dp_fn = graph.function("dp1_user_data");
    let dp = graph.call_site(&dp_fn);

    assert!(get.output().flows_to_data(&send.input()));
    assert!(get2.output().flows_to_data(&send2.input()));
    assert!(get2.output().flows_to_data(&dp.input()));
    assert!(!get.output().flows_to_data(&dp.input()));

    assert!(!get.output().flows_to_data(&send2.input()));
    assert!(!get2.output().flows_to_data(&send.input()));
});

// Inspired by sled::arc::Arc::make_mut, when instantiating `T` to `Config`
#[test]
fn projections_after_deref() {
    InlineTestBuilder::new(stringify!(
        use std::sync::atomic::AtomicUsize;

        #[repr(C)]
        struct ArcInner<T: ?Sized> {
            rc: AtomicUsize,
            inner: T,
        }

        pub struct Arc<T: ?Sized> {
            ptr: *mut ArcInner<T>,
        }

        #[derive(Clone)]
        struct Config {
            a: i32,
            b: i32,
            c: i32,
            d: i32,
            e: i32,
        }

        impl<T: ?Sized> std::ops::Deref for Arc<T> {
            type Target = T;

            fn deref(&self) -> &T {
                unsafe { &(*self.ptr).inner }
            }
        }

        impl<T: Clone> Arc<T> {
            pub fn make_mut(arc: &mut Self) -> &mut T {
                *arc = Arc::new((**arc).clone());
                unsafe { &mut arc.ptr.as_mut().unwrap().inner }
            }
        }

        impl<T> Arc<T> {
            pub fn new(inner: T) -> Arc<T> {
                let bx = Box::new(ArcInner {
                    inner,
                    rc: AtomicUsize::new(1),
                });
                let ptr = Box::into_raw(bx);
                Arc { ptr }
            }
        }

        fn main() {
            let mut a = Arc::new(Config {
                a: 1,
                b: 2,
                c: 3,
                d: 4,
                e: 5,
            });
            let b = Arc::make_mut(&mut a);
            b.a = 10;
            println!("{:?}", b.a);
        }
    ))
    .check_ctrl(|_| ());
}
