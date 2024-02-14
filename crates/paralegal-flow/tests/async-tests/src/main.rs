// extern crate async_std;
// use async_std::prelude::*;

#[paralegal::marker(source)]
fn get_user_data() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}
#[paralegal::marker(source)]
fn get_user_data2() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}
#[paralegal::marker(
    yey_paralegal_flow_now_needs_this_label_or_it_will_recurse_into_this_function,
    return
)]
fn dp_user_data(user_data: &mut UserData) {
    for i in &mut user_data.data {
        *i = 2;
    }
}

#[paralegal::marker{ sink, arguments = [0] }]
fn send_user_data(user_data: &UserData) {}

#[paralegal::marker{ sink, arguments = [0] }]
fn send_user_data2(user_data: &UserData) {}

#[paralegal::marker(source)]
async fn async_get_user_data() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}

#[paralegal::marker(
    yey_paralegal_flow_now_needs_this_label_or_it_will_recurse_into_this_function,
    return
)]
async fn async_dp_user_data(user_data: &mut UserData) {
    for i in &mut user_data.data {
        *i = 2;
    }
}

async fn inlineable_async_dp_user_data(user_data: &mut UserData) {
    dp_user_data(user_data)
}

#[paralegal::marker{ sink, arguments = [0] }]
async fn async_send_user_data(user_data: &UserData) {}

#[paralegal::marker(sensitive)]
struct UserData {
    pub data: Vec<i64>,
}
#[paralegal::analyze]
async fn top_level_inlining_happens() {
    let mut user_data = get_user_data();
    dp_user_data(&mut user_data);
    send_user_data(&user_data);
}

#[paralegal::analyze]
async fn awaiting_works() {
    let mut user_data = async_get_user_data().await;
    async_dp_user_data(&mut user_data).await;
    async_send_user_data(&user_data).await;
}

#[paralegal::analyze]
async fn two_data_over_boundary() {
    let user_data1 = get_user_data();
    let user_data2 = get_user_data2();
    let _ = async_get_user_data().await;
    send_user_data(&user_data1);
    send_user_data2(&user_data2);
}

#[paralegal::analyze]
async fn arguments_work(d: UserData) {
    send_user_data(&d);
}

#[paralegal::analyze]
async fn inlining_crate_local_async_fns() {
    let mut user_data = get_user_data();
    inlineable_async_dp_user_data(&mut user_data).await;
    send_user_data(&user_data);
}

async fn arity2_inlineable_async_dp_user_data(_: &mut UserData, user_data: &mut UserData) {
    dp_user_data(user_data)
}

#[paralegal::analyze]
async fn no_inlining_overtaint() {
    let mut ud1 = get_user_data();
    let mut ud2 = get_user_data2();
    arity2_inlineable_async_dp_user_data(&mut ud1, &mut ud2).await;
    send_user_data(&ud1);
    send_user_data2(&ud2);
}

async fn arity2_inlineable_async_dp_user_data2(_: &UserData, user_data: &mut UserData) {
    dp_user_data(user_data)
}

#[paralegal::analyze]
async fn no_mixed_mutability_borrow_inlining_overtaint() {
    let mut ud1 = get_user_data();
    let mut ud2 = get_user_data2();
    arity2_inlineable_async_dp_user_data2(&ud1, &mut ud2).await;
    send_user_data(&ud1);
    send_user_data2(&ud2);
}

async fn send_both(ud1: &UserData, ud2: &UserData) {
    send_user_data(&ud1);
    send_user_data2(&ud2);
}

#[paralegal::analyze]
async fn no_immutable_inlining_overtaint() {
    let mut ud1 = get_user_data();
    let mut ud2 = get_user_data2();
    send_both(&ud1, &ud2).await;
}

async fn send_both2(ud1: &UserData, ud2: &mut UserData) {
    send_user_data(&ud1);
    send_user_data2(&ud2);
}

#[paralegal::analyze]
async fn no_mixed_mutability_inlining_overtaint() {
    let mut ud1 = get_user_data();
    let mut ud2 = get_user_data2();
    send_both2(&ud1, &mut ud2).await;
}

async fn move_send_both(ud1: UserData, ud2: UserData) {
    send_user_data(&ud1);
    send_user_data2(&ud2);
}

#[paralegal::analyze]
async fn no_value_inlining_overtaint() {
    let mut ud1 = get_user_data();
    let mut ud2 = get_user_data2();
    move_send_both(ud1, ud2).await;
}

#[paralegal::marker(noinline)]
async fn f() -> usize {
    0
}

#[paralegal::marker(noinline)]
fn some_input() -> usize {
    0
}

#[paralegal::marker(noinline)]
fn another_input() -> usize {
    9
}

#[paralegal::marker(target)]
fn target(i: usize) {}

#[paralegal::marker(target)]
fn another_target(i: usize) {}

async fn id_fun<T>(t: T) -> T {
    let _ = f();
    t
}

#[paralegal::analyze]
async fn remove_poll_match() {
    let p = some_input();
    let x = f().await;
    let y = target(p);
    ()
}

#[paralegal::analyze]
async fn no_overtaint_over_poll() {
    let p = some_input();
    let q = another_input();
    let t = id_fun((p, q)).await;
    target(t.0);
    another_target(t.1);
}

#[paralegal::analyze]
async fn return_from_async() -> usize {
    some_input()
}

#[paralegal::analyze]
async fn async_return_from_async() -> usize {
    id_fun(some_input()).await
}

fn main() {}
