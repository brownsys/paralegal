#![feature(register_tool)]
#![register_tool(dfpp)]


// extern crate async_std;
// use async_std::prelude::*;

#[dfpp::label(source)]
fn get_user_data() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}
#[dfpp::label(source)]
fn get_user_data2() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}
#[dfpp::label(yey_dfpp_now_needs_this_label_or_it_will_recurse_into_this_function, return)]
fn dp_user_data(user_data: &mut UserData) {
    for i in &mut user_data.data {
        *i = 2;
    }
}

#[dfpp::label{ sink, arguments = [0] }]
fn send_user_data(user_data: &UserData) {}

#[dfpp::label{ sink, arguments = [0] }]
fn send_user_data2(user_data: &UserData) {}

#[dfpp::label(source)]
async fn async_get_user_data() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
} 

#[dfpp::label(yey_dfpp_now_needs_this_label_or_it_will_recurse_into_this_function, return)]
async fn async_dp_user_data(user_data: &mut UserData) {
    for i in &mut user_data.data {
        *i = 2;
    }
}

#[dfpp::label{ sink, arguments = [0] }]
async fn async_send_user_data(user_data: &UserData) {}

#[dfpp::label(sensitive)]
struct UserData {
    pub data: Vec<i64>,
}
#[dfpp::analyze]
async fn basic_happens_before() {
    let mut user_data = get_user_data();
    dp_user_data(&mut user_data);
    send_user_data(&user_data);
}

#[dfpp::analyze]
async fn awaiting_happens_before() {
    let mut user_data = async_get_user_data().await;
    async_dp_user_data(&mut user_data).await;
    async_send_user_data(&user_data).await;
}

#[dfpp::analyze]
async fn two_data_over_boundary() {
    let user_data1 = get_user_data();
    let user_data2 = get_user_data2();
    let _ = async_get_user_data().await;
    send_user_data(&user_data1);
    send_user_data2(&user_data2);
}

fn main() {}