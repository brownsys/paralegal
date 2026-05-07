#![feature(rustc_private)]

use paralegal_flow::{inline_test, test_utils::*};

const EXTRA_ARGS: [&str; 2] = ["--include=crate", "--no-adaptive-approximation"];

#[test]
fn process_basic() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(checks, arguments = [0])]
        fn check_user_data(_: &UserData) -> bool { true }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(_: &UserData) {}

        fn main() {
            let user_data = get_user_data();
            check_user_data(&user_data);
            send_user_data(&user_data);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let check_fn = graph.function("check_user_data");
        let check = graph.call_site(&check_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);

        assert!(get.output().flows_to_data(&check.input()));
        assert!(!check.output().flows_to_data(&send.input()));
        assert!(get.output().flows_to_data(&send.input()));
        assert!(get.output().never_happens_before_data(&check.output(), &send.input()));
    });
}

#[test]
fn process_if() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(checks, arguments = [0])]
        fn check_user_data(_: &UserData) -> bool { true }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(_: &UserData) {}

        fn main() {
            let user_data = get_user_data();
            if check_user_data(&user_data) {
                send_user_data(&user_data);
            }
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let check_fn = graph.function("check_user_data");
        let check = graph.call_site(&check_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);

        assert!(get.output().flows_to_data(&check.input()));
        assert!(get.output().flows_to_data(&send.input()));
        assert!(check.output().influences_next_control(&send.input()));
    });
}

#[test]
fn process_if_after() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(checks, arguments = [0])]
        fn check_user_data(_: &UserData) -> bool { true }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(_: &UserData) {}

        #[paralegal_flow::marker(noinline, return)]
        fn modify(_: &mut UserData) {}

        fn main() {
            let mut user_data = get_user_data();
            if check_user_data(&user_data) {
                modify(&mut user_data);
            }
            send_user_data(&user_data);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let check_fn = graph.function("check_user_data");
        let check = graph.call_site(&check_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);
        let modify_fn = graph.function("modify");
        let modify = graph.call_site(&modify_fn);

        assert!(get.output().flows_to_data(&check.input()));
        assert!(check.output().influences_next_control(&modify.input()));
        assert!(modify.output().flows_to_data(&send.input()));
        assert!(!check.output().influences_next_control(&send.output()));
    });
}

#[test]
fn process_nested_if() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(checks, arguments = [0])]
        fn check_user_data(_: &UserData) -> bool { true }

        #[paralegal_flow::marker(checks, arguments = [0])]
        fn check2(_: &UserData) -> bool { true }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(_: &UserData) {}

        fn main() {
            let user_data = get_user_data();
            if check_user_data(&user_data) {
                if check2(&user_data) {
                    send_user_data(&user_data);
                }
            }
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let check_fn = graph.function("check_user_data");
        let check = graph.call_site(&check_fn);
        let check2_fn = graph.function("check2");
        let check2 = graph.call_site(&check2_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);

        assert!(get.output().flows_to_data(&check.input()));
        assert!(get.output().flows_to_data(&check2.input()));
        assert!(get.output().flows_to_data(&send.input()));
        assert!(check.output().influences_next_control(&check2.input()));
        assert!(check2.output().influences_next_control(&send.input()));
    });
}

#[test]
fn process_if_multiple_statements() {
    InlineTestBuilder::new(stringify!(
        #[paralegal_flow::marker(sensitive)]
        struct UserData {
            pub data: Vec<i64>,
        }
        #[paralegal_flow::marker{ sink, arguments = [0] }]
        fn send_user_data(_user_data: &UserData) {}

        #[paralegal_flow::marker{checks, arguments = [0]}]
        fn check_user_data(user_data: &UserData) -> bool {
            for i in &user_data.data {
                if i < &0 {
                    return false;
                }
            }
            return true;
        }
        #[paralegal_flow::marker{ noinline, return }]
        fn modify(_user_data: &mut UserData) {}

        #[paralegal_flow::marker{source, return}]
        fn get_user_data() -> UserData {
            return UserData {
                data: vec![1, 2, 3],
            };
        }
        fn main() {
            let mut user_data = get_user_data();
            if check_user_data(&user_data) {
                modify(&mut user_data);
                send_user_data(&user_data);
            }
        }
    ))
    .check_ctrl(|graph| {
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let check_fn = graph.function("check_user_data");
        let check = graph.call_site(&check_fn);
        let modify_fn = graph.function("modify");
        let modify = graph.call_site(&modify_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);

        assert!(get.output().flows_to_data(&check.input()));
        assert!(get.output().flows_to_data(&modify.input()));
        assert!(modify.output().flows_to_data(&send.input()));
        assert!(check.output().influences_next_control(&modify.input()));
        assert!(check.output().influences_next_control(&send.input()));
        assert!(!modify.output().influences_next_control(&send.input()));
    });
}

#[test]
fn process_if_not_function_call() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(noinline, return)]
        fn get_x() -> i64 { 5 }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(_: &UserData) {}

        #[paralegal_flow::marker(noinline, return)]
        fn modify(_: &mut UserData) {}

        fn main() {
            let x = get_x();
            let mut user_data = get_user_data();
            if x > 5 {
                modify(&mut user_data);
            }
            send_user_data(&user_data);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let getx_fn = graph.function("get_x");
        let getx = graph.call_site(&getx_fn);
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let modify_fn = graph.function("modify");
        let modify = graph.call_site(&modify_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);

        assert!(!getx.output().flows_to_data(&get.input()));
        assert!(getx.output().influences_next_control(&modify.input()));
        assert!(modify.output().flows_to_data(&send.input()));
        assert!(!getx.output().influences_next_control(&send.output()));
    });
}

#[test]
fn process_no_args() {
    inline_test! {
        #[paralegal_flow::marker(sensitive)]
        struct UserData { pub data: Vec<i64> }

        #[paralegal_flow::marker(noinline, return)]
        fn get_x() -> i64 { 5 }

        #[paralegal_flow::marker(source, return)]
        fn get_user_data() -> UserData { UserData { data: vec![1, 2, 3] } }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn send_user_data(_: &UserData) {}

        fn main() {
            let x = get_x();
            let mut user_data = UserData { data: vec![] };
            if x > 5 {
                user_data = get_user_data();
            }
            send_user_data(&user_data);
        }
    }
    .with_extra_args(EXTRA_ARGS)
    .check_ctrl(|graph| {
        let getx_fn = graph.function("get_x");
        let getx = graph.call_site(&getx_fn);
        let get_fn = graph.function("get_user_data");
        let get = graph.call_site(&get_fn);
        let send_fn = graph.function("send_user_data");
        let send = graph.call_site(&send_fn);

        assert!(getx.output().flows_to_any(&get.output()));
        assert!(get.output().flows_to_data(&send.input()));
        assert!(getx.output().flows_to_any(&send.input()));
        assert!(getx.output().influences_next_control(&get.output()));
    });
}

#[test]
fn cross_function_control_flow() {
    inline_test! {
        fn main() -> Result<(), ()> {
            has_influence()?;
            wrapper();
            Ok(())
        }

        fn wrapper() {
            influenced();
        }

        #[paralegal_flow::marker(has_influence, return)]
        fn has_influence() -> Result<(), ()> {
            Ok(())
        }

        #[paralegal_flow::marker(influenced, return)]
        fn influenced() {}
    }
    .check_ctrl(|ctrl| {
        let has_influence = ctrl.marked("has_influence");
        let influenced = ctrl.marked("influenced");

        dbg!(&ctrl.spdg().markers);

        assert!(!has_influence.is_empty());
        assert!(!influenced.is_empty());

        assert!(has_influence.influences_ctrl(&influenced));
    });
}

#[test]
fn cross_function_control_flow_with_skip_simple() {
    inline_test! {
        fn main() -> Result<(), ()> {
            has_influence()?;
            wrapper();
            Ok(())
        }

        fn wrapper() {
            skip();
        }

        fn skip() {
            influenced();
        }

        #[paralegal_flow::marker(has_influence, return)]
        fn has_influence() -> Result<(), ()> {
            Ok(())
        }

        #[paralegal_flow::marker(influenced, return)]
        fn influenced() {
        }
    }
    .check_ctrl(|ctrl| {
        let has_influence = ctrl.marked("has_influence");
        let influenced = ctrl.marked("influenced");

        assert!(!has_influence.is_empty());
        assert!(!influenced.is_empty());

        assert!(has_influence.influences_ctrl(&influenced));
    });
}

#[test]
fn cross_function_control_flow_with_skip_complex() {
    inline_test! {
        fn main() -> Result<(), ()> {
            let mut result = 0;
            let status = has_influence()?;
            result += 1;
            let mut values = vec![1, 2, 3];
            for v in &mut values {
                *v += result;
            }
            if values.iter().sum::<i32>() > no_influence() {
            } else {
                result -= 1;
            }
            wrapper();
            let _final_check = result * values.len() as i32;
            Ok(())
        }

        fn wrapper() {
            skip();
        }

        fn skip() {
            influenced();
        }

        #[paralegal_flow::marker(has_influence, return)]
        fn has_influence() -> Result<(), ()> {
            Ok(())
        }
        #[paralegal_flow::marker(no_influence, return)]
        fn no_influence() -> i32 {
            0
        }

        #[paralegal_flow::marker(influenced, return)]
        fn influenced() {
        }
    }
    .check_ctrl(|ctrl| {
        let has_influence = ctrl.marked("has_influence");
        let influenced = ctrl.marked("influenced");
        let no_influence = ctrl.marked("no_influence");

        assert!(!has_influence.is_empty());
        assert!(!influenced.is_empty());
        assert!(!no_influence.is_empty());

        assert!(has_influence.influences_ctrl(&influenced));
        assert!(!no_influence.influences_ctrl(&influenced));
    });
}
