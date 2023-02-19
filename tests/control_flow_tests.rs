#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use dfpp::Symbol;
mod helpers;
use helpers::*;

fn do_in_crate_dir<A, F: std::panic::UnwindSafe + FnOnce() -> A>(f: F) -> std::io::Result<A> {
    with_current_directory("tests/control-flow-tests", f)
}

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = *helpers::DFPP_INSTALLED
        && do_in_crate_dir(|| { run_dfpp_with_graph_dump() }).map_or_else(
            |e| {
                println!("io err {}", e);
                false
            },
            |t| t
        );
}

macro_rules! define_test {
    ($name:ident : $graph:ident -> $block:block) => {
        #[test]
        fn $name() {
            assert!(*TEST_CRATE_ANALYZED);
            use_rustc(|| {
                let $graph =
                    do_in_crate_dir(|| G::from_file(Symbol::intern(stringify!($name)))).unwrap();
                $block
            });
        }
    };
}

define_test!(process_basic : graph -> {
    let get = graph.function_call("get_user_data");
    let check = graph.function_call("check_user_data");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &check));
    assert!(!graph.connects(&check, &send));
    assert!(graph.connects(&get, &send));
    assert!(graph.connects_direct(&get, &send));
});

define_test!(process_if : graph -> {
    let get = graph.function_call("get_user_data");
    let check = graph.function_call("check_user_data");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &check));
    assert!(graph.connects(&check, &send));
    assert!(graph.connects(&get, &send));
    assert!(graph.connects_direct(&get, &send));
    assert!(graph.connects_direct(&check, &send));
});

define_test!(process_if_after : graph -> {
    let get = graph.function_call("get_user_data");
    let check = graph.function_call("check_user_data");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &check));
    assert!(graph.connects(&check, &send));
    assert!(graph.connects(&get, &send));
    assert!(graph.connects_direct(&get, &send));
    assert!(!graph.connects_direct(&check, &send));
});

define_test!(process_nested_if : graph -> {
    let get = graph.function_call("get_user_data");
    let check = graph.function_call("check_user_data");
    let check2 = graph.function_call("check2");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &check));
    assert!(graph.connects(&check, &send));
    assert!(graph.connects(&check2, &send));
    assert!(graph.connects(&get, &send));
    assert!(graph.connects_direct(&get, &send));
    assert!(graph.connects_direct(&check, &check2));
    assert!(graph.connects_direct(&check2, &send));
});

define_test!(process_if_multiple_statements : graph -> {
    let get = graph.function_call("get_user_data");
    let check = graph.function_call("check_user_data");
    let modify = graph.function_call("modify");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&get, &check));
    assert!(graph.connects(&check, &modify));
    assert!(graph.connects(&check, &send));
    assert!(graph.connects(&get, &send));
    assert!(!graph.connects_direct(&get, &send));
    assert!(graph.connects_direct(&check, &modify));
    assert!(graph.connects_direct(&check, &send));
    assert!(graph.connects_direct(&modify, &send));
});

define_test!(process_if_not_function_call : graph -> {
    let getx = graph.function_call("get_x");
    let get = graph.function_call("get_user_data");
    let modify = graph.function_call("modify");
    let send = graph.function_call("send_user_data");

    assert!(!graph.connects(&getx, &get));
    assert!(graph.connects_direct(&get, &send));
    assert!(graph.connects_direct(&getx, &modify));
    assert!(graph.connects(&getx, &send));
    assert!(!graph.connects_direct(&getx, &send));
});

define_test!(process_no_args : graph -> {
    let getx = graph.function_call("get_x");
    let get = graph.function_call("get_user_data");
    let send = graph.function_call("send_user_data");

    assert!(graph.connects(&getx, &get));
    assert!(graph.connects(&get, &send));
    assert!(graph.connects(&getx, &send));
    assert!(graph.connects_direct(&get, &send));
    assert!(graph.connects_direct(&getx, &get));
});
