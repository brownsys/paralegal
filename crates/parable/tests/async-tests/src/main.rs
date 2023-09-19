#![feature(register_tool)]
#![register_tool(parable)]


// extern crate async_std;
// use async_std::prelude::*;

#[parable::label(source)]
fn get_user_data() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}
#[parable::label(source)]
fn get_user_data2() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}
#[parable::label(yey_parable_now_needs_this_label_or_it_will_recurse_into_this_function, return)]
fn dp_user_data(user_data: &mut UserData) {
    for i in &mut user_data.data {
        *i = 2;
    }
}

#[parable::label{ sink, arguments = [0] }]
fn send_user_data(user_data: &UserData) {}

#[parable::label{ sink, arguments = [0] }]
fn send_user_data2(user_data: &UserData) {}

#[parable::label(source)]
async fn async_get_user_data() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
} 

#[parable::label(yey_parable_now_needs_this_label_or_it_will_recurse_into_this_function, return)]
async fn async_dp_user_data(user_data: &mut UserData) {
    for i in &mut user_data.data {
        *i = 2;
    }
}

async fn inlineable_async_dp_user_data(user_data: &mut UserData) {
    dp_user_data(user_data)
}



#[parable::label{ sink, arguments = [0] }]
async fn async_send_user_data(user_data: &UserData) {}

#[parable::label(sensitive)]
struct UserData {
    pub data: Vec<i64>,
}
#[parable::analyze]
async fn top_level_inlining_happens() {
    let mut user_data = get_user_data();
    dp_user_data(&mut user_data);
    send_user_data(&user_data);
}

#[parable::analyze]
async fn awaiting_works() {
    let mut user_data = async_get_user_data().await;
    async_dp_user_data(&mut user_data).await;
    async_send_user_data(&user_data).await;
}

#[parable::analyze]
async fn two_data_over_boundary() {
    let user_data1 = get_user_data();
    let user_data2 = get_user_data2();
    let _ = async_get_user_data().await;
    send_user_data(&user_data1);
    send_user_data2(&user_data2);
}

#[parable::analyze]
async fn arguments_work(d: UserData) {
    send_user_data(&d);
}

#[parable::analyze]
async fn inlining_crate_local_async_fns() {
    let mut user_data = get_user_data();
    inlineable_async_dp_user_data(&mut user_data).await;
    send_user_data(&user_data);
}





async fn arity2_inlineable_async_dp_user_data(_: &mut UserData, user_data: &mut UserData) {
    dp_user_data(user_data)
}

#[parable::analyze]
async fn no_inlining_overtaint() {
    let mut ud1 = get_user_data();
    let mut ud2 = get_user_data2();
    arity2_inlineable_async_dp_user_data(&mut ud1, &mut ud2);
    send_user_data(&ud1);
    send_user_data2(&ud2);
}





async fn send_both(ud1: &UserData, ud2: &UserData) {
    send_user_data(&ud1);
    send_user_data2(&ud2);
}

#[parable::analyze]
async fn no_immutable_inlining_overtaint() {
    let mut ud1 = get_user_data();
    let mut ud2 = get_user_data2();
    send_both(&ud1, &ud2);
}

#[parable::label(noinline)]
async fn f() -> usize {
    0
}

#[parable::label(noinline)]
fn some_input() -> usize {
    0
}

#[parable::label(noinline)]
fn another_input() -> usize {
    9
}

#[parable::label(target)]
fn target(i: usize) {

}

#[parable::label(target)]
fn another_target(i: usize) {

}

async fn id_fun<T>(t: T) -> T {
    let _ = f();
    t
}

#[parable::analyze]
async fn remove_poll_match() {
    let p = some_input();
    let x = f().await;
    let y = target(p);
    ()
}

#[parable::analyze]
async fn no_overtaint_over_poll() {
    let p = some_input();
    let q = another_input();
    let t = id_fun((p, q)).await;
    target(t.0);
    another_target(t.1);
}


fn main() {}