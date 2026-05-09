#![feature(rustc_private)]

use paralegal_flow::{inline_test, test_utils::*};

const EXTRA_ARGS: [&str; 2] = ["--include=crate", "--no-adaptive-approximation"];

#[test]
fn track_mutable_modify() {
    inline_test! {
        struct S {
            field: u32,
            field2: u32,
        }

        #[paralegal_flow::marker(noinline, return)]
        fn new_s() -> S {
            S { field: 0, field2: 1 }
        }

        #[paralegal_flow::marker(noinline, return)]
        fn modify_it(x: &mut u32) {}

        #[paralegal_flow::marker(noinline)]
        fn read<T>(t: &T) {}

        fn main() {
            let mut x = new_s();
            modify_it(&mut x.field);
            read(&x)
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
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
}

#[test]
#[ignore = "Returning references has undecided PDG semantics. See \
    https://github.com/willcrichton/flowistry/issues/90"]
fn eliminate_return_connection() {
    inline_test! {
        struct S {
            field: u32,
            field2: u32,
        }

        #[paralegal_flow::marker(noinline, return)]
        fn new_s() -> S {
            S { field: 0, field2: 1 }
        }

        #[paralegal_flow::marker(noinline)]
        fn deref_t(s: &S) -> &String {
            unimplemented!()
        }

        #[paralegal_flow::marker(noinline)]
        fn read<T>(t: &T) {}

        fn main() {
            let s = new_s();
            let t = deref_t(&s);
            read(t);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let source_fn = graph.function("new_s");
        let source = graph.call_site(&source_fn);
        let pass_through_fn = graph.function("deref_t");
        let pass_through = graph.call_site(&pass_through_fn);
        let read_fn = graph.function("read");
        let read = graph.call_site(&read_fn);

        assert!(
            dbg!(source.output())
                .always_happens_before_data(&dbg!(pass_through.output()), &dbg!(read.input()))
        );
    });
}

#[test]
fn eliminate_mut_input_connection() {
    inline_test! {
        struct S {
            field: u32,
            field2: u32,
        }

        #[paralegal_flow::marker(noinline, return)]
        fn new_s() -> S {
            S { field: 0, field2: 1 }
        }

        #[paralegal_flow::marker(noinline)]
        fn read<T>(t: &T) {}

        fn main() {
            let s: S = new_s();
            let mut v = Vec::new();
            v.push(&s);
            read(&v);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let source_fn = graph.function("new_s");
        let source = graph.call_site(&source_fn);
        let push_fn = graph.function("push");
        let push = graph.call_site(&push_fn);
        let read_fn = graph.function("read");
        let read = graph.call_site(&read_fn);

        assert!(source.output().is_neighbor_data(&push.input()));
        assert!(push.output().is_neighbor_data(&read.input()));
    });
}

#[test]
#[ignore = "Alias analysis is configured to abstract via lifetimes only at the moment. \
    See https://github.com/willcrichton/flowistry/issues/93"]
fn input_elimination_isnt_a_problem_empty() {
    inline_test! {
        struct S {
            field: u32,
            field2: u32,
        }

        #[paralegal_flow::marker(noinline, return)]
        fn new_s() -> S {
            S { field: 0, field2: 1 }
        }

        #[paralegal_flow::marker(noinline)]
        fn read<T>(t: &T) {}

        fn insert_ref<'v, 't: 'v, T>(v: &mut Vec<&'v T>, t: &'t T) {}

        fn main() {
            let x = new_s();
            let mut v = Vec::new();
            insert_ref(&mut v, &x);
            read(&v);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let source_fn = graph.function("new_s");
        let source = graph.call_site(&source_fn);
        let read_fn = graph.function("read");
        let read = graph.call_site(&read_fn);

        assert!(!source.output().flows_to_data(&read.input()));
    });
}

#[test]
fn input_elimination_isnt_a_problem_vec_push() {
    inline_test! {
        struct S {
            field: u32,
            field2: u32,
        }

        #[paralegal_flow::marker(noinline, return)]
        fn new_s() -> S {
            S { field: 0, field2: 1 }
        }

        #[paralegal_flow::marker(noinline)]
        fn read<T>(t: &T) {}

        fn insert_ref_2<'v, 't: 'v, T>(v: &mut Vec<&'v T>, t: &'t T) {
            v.push(t)
        }

        fn main() {
            let x = new_s();
            let mut v = Vec::new();
            v.insert(0, &x);
            insert_ref_2(&mut v, &x);
            read(&v);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
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
        assert!(
            insert
                .output()
                .always_happens_before_data(&push.output(), &read.input())
        );
    });
}

#[test]
fn input_elimination_isnt_a_problem_statement() {
    inline_test! {
        struct S {
            field: u32,
            field2: u32,
        }

        #[paralegal_flow::marker(noinline, return)]
        fn new_s() -> S {
            S { field: 0, field2: 1 }
        }

        #[paralegal_flow::marker(noinline)]
        fn another_s() -> S {
            unimplemented!()
        }

        #[paralegal_flow::marker(noinline)]
        fn read<T>(t: &T) {}

        struct T<'a> {
            field: &'a S,
        }

        #[paralegal_flow::marker(noinline)]
        fn new_t<'a>() -> T<'a> {
            unimplemented!()
        }

        #[paralegal_flow::marker(noinline)]
        fn assoc<'a, 'b: 'a>(x: &mut T<'a>, s: &'b S) {}

        fn main() {
            let ref r = new_s();
            let ref r2 = another_s();
            let mut x = new_t();
            assoc(&mut x, r);
            x.field = r2;
            read(&x);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
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
    });
}

#[test]
fn no_inlining_overtaint() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData {
            pub data: Vec<i64>,
        }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData {
            UserData { data: vec![1, 2, 3] }
        }

        #[paralegal_flow::marker(source, return)]
        fn get2_user_data() -> UserData {
            UserData { data: vec![1, 2, 3] }
        }

        #[paralegal_flow::marker(yey_paralegal_flow_now_needs_this_label_or_it_will_recurse_into_this_function, return)]
        fn dp1_user_data(user_data: &mut UserData) {
            for i in &mut user_data.data {
                *i = 2;
            }
        }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(user_data: &UserData) {}

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send2_user_data(user_data: &UserData) {}

        fn arity2_inlineable_async_dp_user_data(ud: &mut (&mut UserData, &mut UserData)) {
            dp1_user_data(ud.1)
        }

        fn main() {
            let mut ud1 = get_user_data();
            let mut ud2 = get2_user_data();
            arity2_inlineable_async_dp_user_data(&mut (&mut ud1, &mut ud2));
            send_user_data(&ud1);
            send2_user_data(&ud2);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
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
}

// Now yes, this doesn't quite fit into this test suite but because the tests
// make such large artifacts, I didn't want to create another test file.
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

#[test]
fn reference_in_struct() {
    InlineTestBuilder::new(stringify!(
        struct Foo<'a> {
            a: &'a i32,
        }

        #[paralegal_flow::marker(target, arguments=[0])]
        fn sink(_a: Foo<'_>) {}

        #[paralegal_flow::marker(source, return)]
        fn source() -> i32 {
            42
        }

        fn main() {
            let a = source();
            let foo = Foo { a: &a };
            sink(foo);
        }
    ))
    .check_ctrl(|graph| {
        let source = graph.marked("source");
        let sink = graph.marked("target");
        assert!(!source.is_empty());
        assert!(!sink.is_empty());
        assert!(source.flows_to_data(&sink));
    });
}

#[test]
fn lemmy_non_monomorphized_place_bug() {
    InlineTestBuilder::new(stringify!(
        trait Trait {
            fn method(&self) -> usize;
        }

        impl<T: Trait> Trait for &T {
            fn method(&self) -> usize {
                (*self).method()
            }
        }

        #[derive(Clone, Copy)]
        enum Foo {
            Usize(usize),
            None
        }

        impl Trait for Foo {
            fn method(&self) -> usize {
                match self {
                    Foo::Usize(x) => *x,
                    Foo::None => 0
                }
            }
        }

        fn inner<T: Trait>(u: &T) -> usize {
            (*u).method()
        }

        struct S<T>{
            f:T,
            f2: usize
        }

        fn pass_through<T: Trait >(s: &S<T>) -> usize {
            inner(&s.f)
        }

        fn main() {
            let foo = Foo::Usize(0);
            let s = S { f: &foo, f2: 0 };
            let result = pass_through(&s);
        }
    ))
    .with_extra_args([
        "--no-adaptive-approximation".to_string(),
        "--dump".to_string(),
        "mir".to_string(),
    ])
    .check_ctrl(|_| ());
}
