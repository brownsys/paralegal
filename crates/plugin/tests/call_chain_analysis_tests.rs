#![feature(rustc_private)]

extern crate rustc_span;

use paralegal_flow::{inline_test, test_utils::*};
use paralegal_pdg::GlobalLocation;
use paralegal_pdg::utils::display_list;
use rustc_span::Symbol;

const EXTRA_ARGS: [&str; 2] = ["--include=crate", "--no-adaptive-approximation"];

/// Property shared by every `no_overtaint_over_*` test below: two distinct
/// sources `left` and `right` are routed through some construction and read
/// back by `left_sink` / `right_sink`. Precision is preserved iff each
/// source flows only to its matching sink.
fn assert_disjoint_flows(graph: &CtrlRef<'_>) {
    let left_fn = graph.function("left");
    let right_fn = graph.function("right");
    let left_sink_fn = graph.function("left_sink");
    let right_sink_fn = graph.function("right_sink");
    let left = graph.call_site(&left_fn);
    let right = graph.call_site(&right_fn);
    let left_sink = graph.call_site(&left_sink_fn);
    let right_sink = graph.call_site(&right_sink_fn);

    assert!(
        left.output().flows_to_data(&left_sink.input()),
        "expected `left` to reach `left_sink`",
    );
    assert!(
        right.output().flows_to_data(&right_sink.input()),
        "expected `right` to reach `right_sink`",
    );
    assert!(
        !left.output().flows_to_data(&right_sink.input()),
        "precision violation: `left` reaches `right_sink`",
    );
    assert!(
        !right.output().flows_to_data(&left_sink.input()),
        "precision violation: `right` reaches `left_sink`",
    );
}

#[test]
fn without_return() {
    inline_test! {
        #[paralegal_flow::marker(hello, return)]
        fn source() -> i32 { 0 }

        fn callee_2(x: i32) {
            receiver(x);
        }

        #[paralegal_flow::marker(there, arguments = [0])]
        fn receiver(_x: i32) {}

        fn main() {
            callee_2(source());
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|ctrl| {
        let src_fn = ctrl.function("source");
        let src = ctrl.call_site(&src_fn);
        let dest_fn = ctrl.function("receiver");
        let dest_sink = ctrl.call_site(&dest_fn);
        let dest = dest_sink.input().nth(0).unwrap();

        assert!(src.output().flows_to_data(&dest));
    });
}

#[test]
fn with_return() {
    InlineTestBuilder::new(stringify!(
        #[paralegal_flow::marker(hello, return)]
        fn source() -> i32 {
            0
        }
        fn callee(x: i32) -> i32 {
            source()
        }
        #[paralegal_flow::marker(there, arguments = [0])]
        fn receiver(x: i32) {}

        fn main(x: i32) {
            receiver(callee(x));
        }
    ))
    .with_extra_args(["--dump".to_string(), "spdg".to_string()])
    .check_ctrl(|ctrl| {
        let src_fn = ctrl.function("source");
        let src = ctrl.call_site(&src_fn);
        let dest_fn = ctrl.function("receiver");
        let dest_sink = ctrl.call_site(&dest_fn);
        let dest = dest_sink.input().nth(0).unwrap();

        assert!(!src.output().is_empty());
        assert!(!dest_sink.input().is_empty());

        assert!(src.output().flows_to_data(&dest));
    })
}

#[test]
fn on_mut_var() {
    inline_test! {
        #[paralegal_flow::marker(hello, return)]
        fn source() -> i32 { 0 }

        fn modify_it(x: &mut i32) {
            *x = source();
        }

        #[paralegal_flow::marker(there, arguments = [0])]
        fn receiver(_x: i32) {}

        fn main() {
            let mut x = 4;
            modify_it(&mut x);
            receiver(x);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|ctrl| {
        let src_fn = ctrl.function("source");
        let src = ctrl.call_site(&src_fn);
        let dest_fn = ctrl.function("receiver");
        let dest_sink = ctrl.call_site(&dest_fn);
        let dest = dest_sink.input().nth(0).unwrap();

        assert!(src.output().flows_to_data(&dest));
    });
}

#[test]
fn on_mut_var_no_modify() {
    inline_test! {
        #[paralegal_flow::marker(hello, return)]
        fn source() -> i32 { 0 }

        fn dont_modify_it(x: &mut i32) -> i32 {
            source()
        }

        #[paralegal_flow::marker(there, arguments = [0])]
        fn receiver(_x: i32) {}

        fn main() {
            let mut x = 4;
            dont_modify_it(&mut x);
            receiver(x);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|ctrl| {
        let src_fn = ctrl.function("source");
        if let Some(src) = ctrl.call_sites(&src_fn).pop() {
            let dest_fn = ctrl.function("receiver");
            if let Some(dest_sink) = ctrl.call_sites(&dest_fn).pop() {
                assert!(!src.output().flows_to_data(&dest_sink.input()));
            }
        }
    });
}

#[test]
fn field_sensitivity() {
    inline_test! {
        #[derive(Clone)]
        struct S {
            usize_field: usize,
            string_field: String,
        }

        #[paralegal_flow::marker(noinline, return)]
        fn read_usize(_u: usize) {}

        #[paralegal_flow::marker(noinline, return)]
        fn read_string(_s: String) {}

        fn modify_a_field(s: &mut S) {
            s.usize_field = produce_usize();
        }

        #[paralegal_flow::marker(noinline, return)]
        fn produce_usize() -> usize { 0 }

        #[paralegal_flow::marker(noinline, return)]
        fn produce_string() -> String { "".to_string() }

        fn main() {
            let distraction = 4;
            let mut s = S {
                usize_field: 0,
                string_field: produce_string(),
            };
            modify_a_field(&mut s);
            read_usize(s.usize_field);
            read_string(s.string_field);
            read_usize(distraction);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|ctrl| {
        let produce_usize_fn = ctrl.function("produce_usize");
        let produce_string_fn = ctrl.function("produce_string");
        let consume_usize_fn = ctrl.function("read_usize");
        let consume_string_fn = ctrl.function("read_string");
        let produce_usize = ctrl.call_site(&produce_usize_fn);
        let produce_string = ctrl.call_site(&produce_string_fn);
        let read_string = ctrl.call_site(&consume_string_fn);
        let read_usizes = ctrl.call_sites(&consume_usize_fn);

        #[derive(Eq, PartialEq, Copy, Clone)]
        enum CallSiteState {
            Unknow,
            Distraction,
            Checked,
        }
        use CallSiteState::*;

        let mut usize_call_sites = [Unknow; 2];
        for (idx, read_usize) in read_usizes.iter().enumerate() {
            usize_call_sites[idx] = if produce_usize.output().flows_to_data(&read_usize.input()) {
                Checked
            } else {
                Distraction
            };
        }
        assert!(!produce_usize.output().flows_to_data(&read_string.input()));
        assert!(produce_string.output().flows_to_data(&read_string.input()));
        assert!(usize_call_sites.contains(&Distraction));
        assert!(usize_call_sites.contains(&Checked));
    });
}

#[test]
fn field_sensitivity_across_clone() {
    inline_test! {
        #[derive(Clone)]
        struct S {
            usize_field: usize,
            string_field: String,
        }

        #[paralegal_flow::marker(noinline, return)]
        fn read_usize(_u: usize) {}

        #[paralegal_flow::marker(noinline, return)]
        fn read_string(_s: String) {}

        #[paralegal_flow::marker(noinline, return)]
        fn produce_usize() -> usize { 0 }

        #[paralegal_flow::marker(noinline, return)]
        fn produce_string() -> String { "".to_string() }

        fn main() {
            let distraction = 4;
            let mut s = S {
                usize_field: produce_usize(),
                string_field: produce_string(),
            };
            let s = (&s).clone();
            read_usize(s.usize_field);
            read_string(s.string_field);
            read_usize(distraction);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|ctrl| {
        let produce_usize_fn = ctrl.function("produce_usize");
        let produce_string_fn = ctrl.function("produce_string");
        let consume_usize_fn = ctrl.function("read_usize");
        let consume_string_fn = ctrl.function("read_string");
        let produce_usize = ctrl.call_site(&produce_usize_fn);
        let produce_string = ctrl.call_site(&produce_string_fn);
        let read_string = ctrl.call_site(&consume_string_fn);
        let read_usizes = ctrl.call_sites(&consume_usize_fn);

        #[derive(Eq, PartialEq, Copy, Clone)]
        enum CallSiteState {
            Unknow,
            Distraction,
            Checked,
        }
        use CallSiteState::*;

        let mut usize_call_sites = [Unknow; 2];
        for (idx, read_usize) in read_usizes.iter().enumerate() {
            usize_call_sites[idx] = if produce_usize.output().flows_to_data(&read_usize.input()) {
                assert!(!produce_string.output().flows_to_data(&read_usize.input()));
                Checked
            } else {
                Distraction
            };
        }
        assert!(!produce_usize.output().flows_to_data(&read_string.input()));
        assert!(produce_string.output().flows_to_data(&read_string.input()));
    });
}

// Boilerplate shared by every `no_overtaint_over_*` test: each sets up
// `left`/`right` source functions and `left_sink`/`right_sink` consumer
// functions, all marked `noinline` so they remain as named call sites.
// `assert_disjoint_flows` (above) checks the precision invariant.

#[test]
fn no_overtaint_over_fn_call() {
    inline_test! {
        #[paralegal_flow::marker(noinline)] fn left() -> u32 { 0 }
        #[paralegal_flow::marker(noinline)] fn right() -> u64 { 0 }
        #[paralegal_flow::marker(noinline)] fn left_sink<T>(_: T) {}
        #[paralegal_flow::marker(noinline)] fn right_sink<T>(_: T) {}

        fn id_fun<T, G>(t: (T, G)) -> (T, G) { t }

        fn main() {
            let t = id_fun((left(), right()));
            left_sink(t.0);
            right_sink(t.1);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| assert_disjoint_flows(&graph));
}

#[test]
fn no_overtaint_over_generic_fn_call() {
    inline_test! {
        #[paralegal_flow::marker(noinline)] fn left() -> u32 { 0 }
        #[paralegal_flow::marker(noinline)] fn right() -> u64 { 0 }
        #[paralegal_flow::marker(noinline)] fn left_sink<T>(_: T) {}
        #[paralegal_flow::marker(noinline)] fn right_sink<T>(_: T) {}

        fn generic_id_fun<T>(t: T) -> T { t }

        fn main() {
            let t = generic_id_fun((left(), right()));
            left_sink(t.0);
            right_sink(t.1);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| assert_disjoint_flows(&graph));
}

#[test]
fn no_overtaint_over_nested_fn_call() {
    inline_test! {
        #[paralegal_flow::marker(noinline)] fn left() -> u32 { 0 }
        #[paralegal_flow::marker(noinline)] fn right() -> u64 { 0 }
        #[paralegal_flow::marker(noinline)] fn left_sink<T>(_: T) {}
        #[paralegal_flow::marker(noinline)] fn right_sink<T>(_: T) {}

        fn forwarder(t: (u32, u64)) { acceptor(t) }

        fn acceptor(t: (u32, u64)) {
            left_sink(t.0);
            right_sink(t.1);
        }

        fn main() {
            forwarder((left(), right()));
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| assert_disjoint_flows(&graph));
}

#[test]
fn no_overtaint_over_field_projection_in_callee() {
    inline_test! {
        #[paralegal_flow::marker(noinline)] fn left() -> u32 { 0 }
        #[paralegal_flow::marker(noinline)] fn right() -> u64 { 0 }
        #[paralegal_flow::marker(noinline)] fn left_sink<T>(_: T) {}
        #[paralegal_flow::marker(noinline)] fn right_sink<T>(_: T) {}

        fn first<T, G>(t: (T, G)) -> T { t.0 }

        fn main() {
            let l = left();
            let r = right();
            // first returns the .0 element, so each sink sees its own
            // source. Precision check: the dropped field must not leak.
            left_sink(first((l, r)));
            right_sink(first((r, l)));
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| assert_disjoint_flows(&graph));
}

#[test]
fn no_overtaint_over_aggregate_construction_in_callee() {
    inline_test! {
        #[paralegal_flow::marker(noinline)] fn left() -> u32 { 0 }
        #[paralegal_flow::marker(noinline)] fn right() -> u64 { 0 }
        #[paralegal_flow::marker(noinline)] fn left_sink<T>(_: T) {}
        #[paralegal_flow::marker(noinline)] fn right_sink<T>(_: T) {}

        fn pair<T, G>(a: T, b: G) -> (T, G) { (a, b) }

        fn main() {
            let r = pair(left(), right());
            left_sink(r.0);
            right_sink(r.1);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| assert_disjoint_flows(&graph));
}

#[test]
fn no_overtaint_over_in_place_field_update() {
    inline_test! {
        #[paralegal_flow::marker(noinline)] fn left() -> u32 { 0 }
        #[paralegal_flow::marker(noinline)] fn right() -> u64 { 0 }
        #[paralegal_flow::marker(noinline)] fn left_sink<T>(_: T) {}
        #[paralegal_flow::marker(noinline)] fn right_sink<T>(_: T) {}

        fn set_first<T, G>(t: &mut (T, G), v: T) { t.0 = v }

        fn main() {
            // Start with an arbitrary value in .0; `set_first` overwrites
            // it with `left()`. After the write, t == (left, right).
            let mut t = (0_u32, right());
            set_first(&mut t, left());
            left_sink(t.0);
            right_sink(t.1);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| assert_disjoint_flows(&graph));
}

// Whole-aggregate variant of the projection-in-callee case: the projected
// field is itself an aggregate, so the inner MIR is `_0 = move _1.0` copying
// a whole sub-tuple. Exercises the same field-aggregation bug as the
// existing identity tests (`no_overtaint_over_fn_call` etc.) but on the
// projection axis.
#[test]
fn no_overtaint_over_nested_field_projection_in_callee() {
    inline_test! {
        #[paralegal_flow::marker(noinline)] fn left() -> u32 { 0 }
        #[paralegal_flow::marker(noinline)] fn right() -> u64 { 0 }
        #[paralegal_flow::marker(noinline)] fn left_sink<T>(_: T) {}
        #[paralegal_flow::marker(noinline)] fn right_sink<T>(_: T) {}

        fn first<T, G>(t: (T, G)) -> T { t.0 }

        fn main() {
            // T = (u32, u64) is itself an aggregate, so `_0 = move _1.0`
            // inside `first` is a whole-sub-aggregate copy.
            let r = first(((left(), right()), 0_u8));
            left_sink(r.0);
            right_sink(r.1);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| assert_disjoint_flows(&graph));
}

// Whole-aggregate variant of the construction-in-callee case: the callee
// builds an outer aggregate one of whose fields is itself a whole aggregate
// passed in by argument, producing `_0 = Aggregate([move _1, ...])` in MIR.
#[test]
fn no_overtaint_over_nested_aggregate_construction_in_callee() {
    inline_test! {
        #[paralegal_flow::marker(noinline)] fn left() -> u32 { 0 }
        #[paralegal_flow::marker(noinline)] fn right() -> u64 { 0 }
        #[paralegal_flow::marker(noinline)] fn left_sink<T>(_: T) {}
        #[paralegal_flow::marker(noinline)] fn right_sink<T>(_: T) {}

        fn wrap<T>(a: T) -> (T, u8) { (a, 0) }

        fn main() {
            let r = wrap((left(), right()));
            left_sink(r.0.0);
            right_sink(r.0.1);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| assert_disjoint_flows(&graph));
}

// Whole-aggregate variant of the in-place-via-&mut case: the callee
// overwrites a field whose own type is an aggregate, so `(*_1).0 = move _2`
// is a whole-aggregate copy.
#[test]
fn no_overtaint_over_nested_in_place_field_update() {
    inline_test! {
        #[paralegal_flow::marker(noinline)] fn left() -> u32 { 0 }
        #[paralegal_flow::marker(noinline)] fn right() -> u64 { 0 }
        #[paralegal_flow::marker(noinline)] fn left_sink<T>(_: T) {}
        #[paralegal_flow::marker(noinline)] fn right_sink<T>(_: T) {}

        fn set_first<T, G>(t: &mut (T, G), v: T) { t.0 = v }

        fn main() {
            // Inner tuple has aggregate type (u32, u64); `set_first`
            // overwrites it as a whole. After the write,
            // t.0 == (left, right).
            let mut t = ((0_u32, 0_u64), 0_u8);
            set_first(&mut t, (left(), right()));
            left_sink(t.0.0);
            right_sink(t.0.1);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| assert_disjoint_flows(&graph));
}

#[test]
fn recursion_breaking_with_k_depth() {
    let mut test = InlineTestBuilder::new(stringify!(
        fn recurses(i: u32) {
            if i > 0 {
                recurses(i - 1);
            }
        }

        #[paralegal_flow::analyze]
        fn main() {
            recurses(10);
        }
    ));
    test.with_extra_args(["--k-depth=3".to_string()])
        .run_with_tcx(|tcx, desc| {
            let ctrl = desc.ctrl("main");
            let css = ctrl.graph().desc.all_call_sites();
            assert!(!css.is_empty(), "Vacuous");
            let target = Symbol::intern("recurses");
            for cs in css.into_iter() {
                assert!(
                    cs.len() <= 4,
                    "Call string over length limit (length {}) {cs} ",
                    cs.len()
                );
                let recursions: Box<[GlobalLocation]> = cs
                    .iter()
                    .filter(|loc| tcx.item_name(loc.function) == target)
                    .collect();
                assert!(
                    recursions.len() <= 1,
                    "Found recursive call strings: {}",
                    display_list(recursions.iter())
                );
                assert!(
                    cs.len() <= 2,
                    "Call string indicates recursion (length {}) {cs}",
                    cs.len()
                );
            }
        })
        .unwrap();
}

#[test]
fn recursion_breaking_with_k_depth_on_main() {
    let mut test = InlineTestBuilder::new(stringify!(
        #[paralegal_flow::analyze]
        fn recurses(i: u32) {
            if i > 0 {
                recurses(i - 1);
            }
        }
    ));
    test.with_extra_args(["--k-depth=1".to_string()])
        .with_entrypoint("recurses".to_string())
        .run_with_tcx(|tcx, desc| {
            let ctrl = desc.ctrl("recurses");
            let css = ctrl.graph().desc.all_call_sites();
            let target = Symbol::intern("recurses");
            assert!(!css.is_empty(), "Vacuous");
            for cs in css.into_iter() {
                assert!(
                    cs.len() <= 2,
                    "Call string over length limit (length {}) {cs} ",
                    cs.len()
                );

                let recursions: Box<[GlobalLocation]> = cs
                    .iter()
                    .filter(|loc| tcx.item_name(loc.function) == target)
                    .collect();
                assert!(
                    recursions.len() <= 1,
                    "Found recursive call strings: {}",
                    display_list(recursions.iter())
                );
                assert!(
                    cs.len() <= 1,
                    "Call string indicates recursion (length {}) {cs}",
                    cs.len()
                );
            }
        })
        .unwrap()
}

#[test]
fn recursion_breaking_with_k_depth_mutual() {
    let mut test = InlineTestBuilder::new(stringify!(
        fn recurses(i: u32) {
            if i > 0 {
                delegator(i);
            }
        }

        fn delegator(i: u32) {
            recurses(i - 1);
        }

        #[paralegal_flow::analyze]
        fn main() {
            recurses(10);
        }
    ));
    test.with_extra_args(["--k-depth=4".to_string()])
        .run_with_tcx(|tcx, desc| {
            let ctrl = desc.ctrl("main");
            let css = ctrl.graph().desc.all_call_sites();
            assert!(!css.is_empty(), "Vacuous");
            let target = Symbol::intern("recurses");
            for cs in css.into_iter() {
                assert!(
                    cs.len() <= 5,
                    "Call string over length limit (length {}) {cs} ",
                    cs.len()
                );
                let recursions: Box<[GlobalLocation]> = cs
                    .iter()
                    .filter(|loc| tcx.item_name(loc.function) == target)
                    .collect();
                assert!(
                    recursions.len() <= 1,
                    "Found recursive call strings: {} in {cs}",
                    display_list(recursions.iter())
                );
                assert!(
                    cs.len() <= 3,
                    "Call string indicates recursion (length {}) {cs}",
                    cs.len()
                );
            }
        })
        .unwrap();
}

#[test]
fn field_propagation_on_socket_addr() {
    inline_test! {
        use std::mem;
        // Moved definitions from libc
        mod c {
            pub type sa_family_t = u16;
            pub type in_port_t = u16;
            pub type in_addr_t = u32;
            pub type socklen_t = u32;
            pub type c_char = i8;
            pub type c_int = i32;
            pub const AF_INET6: c_int = 10;
            pub const AF_INET: c_int = 2;
            pub struct in_addr {
                pub s_addr: in_addr_t,
            }
            #[repr(C)]
            pub struct sockaddr_in {
                pub sin_family: sa_family_t,
                pub sin_port: in_port_t,
                pub sin_addr: in_addr,
                pub sin_zero: [u8; 8],
            }
            #[repr(C, align(4))]
            pub struct in6_addr {
                pub s6_addr: [u8; 16],
            }
            #[repr(C)]
            pub struct sockaddr_in6 {
                pub sin6_family: sa_family_t,
                pub sin6_port: in_port_t,
                pub sin6_flowinfo: u32,
                pub sin6_addr: in6_addr,
                pub sin6_scope_id: u32,
            }
            #[repr(C)]
            pub struct sockaddr {
                pub sa_family: sa_family_t,
                pub sa_data: [c_char; 14],
            }
        }
        pub enum SocketAddr {
            V4(SocketAddrV4),
            V6(SocketAddrV6),
        }
        #[derive(Clone, Copy)]
        pub struct SocketAddrV4 {
            ip: Ipv4Addr,
            port: u16,
        }
        #[derive(Clone, Copy)]
        pub struct Ipv4Addr {
            octets: [u8; 4],
        }

        impl Ipv4Addr {
            pub const fn octets(&self) -> [u8; 4] {
                self.octets
            }
        }
        #[derive(Clone, Copy)]
        pub struct Ipv6Addr {
            octets: [u8; 16],
        }
        impl Ipv6Addr {
            pub const fn octets(&self) -> [u8; 16] {
                self.octets
            }
        }
        impl SocketAddrV4 {
            pub const fn ip(&self) -> &Ipv4Addr {
                &self.ip
            }
            pub const fn port(&self) -> u16 {
                self.port
            }
        }
        #[derive(Clone, Copy)]
        pub struct SocketAddrV6 {
            ip: Ipv6Addr,
            port: u16,
            flowinfo: u32,
            scope_id: u32,
        }
        impl SocketAddrV6 {
            pub const fn ip(&self) -> &Ipv6Addr {
                &self.ip
            }
            pub const fn port(&self) -> u16 {
                self.port
            }
            pub const fn flowinfo(&self) -> u32 {
                self.flowinfo
            }
            pub const fn scope_id(&self) -> u32 {
                self.scope_id
            }
        }
        impl IntoInner<c::sockaddr_in> for SocketAddrV4 {
            fn into_inner(self) -> c::sockaddr_in {
                c::sockaddr_in {
                    sin_family: c::AF_INET as c::sa_family_t,
                    sin_port: self.port().to_be(),
                    sin_addr: self.ip().into_inner(),
                    ..unsafe { mem::zeroed() }
                }
            }
        }

        impl IntoInner<c::sockaddr_in6> for SocketAddrV6 {
            fn into_inner(self) -> c::sockaddr_in6 {
                c::sockaddr_in6 {
                    sin6_family: c::AF_INET6 as c::sa_family_t,
                    sin6_port: self.port().to_be(),
                    sin6_addr: self.ip().into_inner(),
                    sin6_flowinfo: self.flowinfo(),
                    sin6_scope_id: self.scope_id(),
                    ..unsafe { mem::zeroed() }
                }
            }
        }
        impl IntoInner<c::in6_addr> for Ipv6Addr {
            fn into_inner(self) -> c::in6_addr {
                c::in6_addr { s6_addr: self.octets() }
            }
        }
        impl IntoInner<c::in_addr> for Ipv4Addr {
            #[inline]
            fn into_inner(self) -> c::in_addr {
                c::in_addr { s_addr: u32::from_ne_bytes(self.octets()) }
            }
        }
        pub trait IntoInner<Inner> {
            fn into_inner(self) -> Inner;
        }

        pub trait FromInner<Inner> {
            fn from_inner(inner: Inner) -> Self;
        }

        #[repr(C)]
        pub(crate) union SocketAddrCRepr {
            v4: c::sockaddr_in,
            v6: c::sockaddr_in6,
        }

        impl SocketAddrCRepr {
            pub fn as_ptr(&self) -> *const c::sockaddr {
                self as *const _ as *const c::sockaddr
            }
        }

        impl<'a> IntoInner<(SocketAddrCRepr, c::socklen_t)> for &'a SocketAddr {
            fn into_inner(self) -> (SocketAddrCRepr, c::socklen_t) {
                match *self {
                    SocketAddr::V4(ref a) => {
                        let sockaddr = SocketAddrCRepr { v4: a.into_inner() };
                        (sockaddr, mem::size_of::<c::sockaddr_in>() as c::socklen_t)
                    }
                    SocketAddr::V6(ref a) => {
                        let sockaddr = SocketAddrCRepr { v6: a.into_inner() };
                        (sockaddr, mem::size_of::<c::sockaddr_in6>() as c::socklen_t)
                    }
                }
            }
        }

        fn main() {
            let addr = SocketAddr::V4(SocketAddrV4 {
                ip: Ipv4Addr { octets: [127, 0, 0, 1] },
                port: 0,
            });
            let _ = (&addr).into_inner();
        }
    }
    .check_ctrl(|_| ());
}
