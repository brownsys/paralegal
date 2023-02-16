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
#[dfpp::label(yey_dfpp_now_needs_this_label_or_it_will_recurse_into_this_function, return)]
fn dp_user_data(user_data: &mut UserData) {
    for i in &mut user_data.data {
        *i = 2;
    }
}


#[dfpp::label{ sink, arguments = [0] }]
fn send_user_data(user_data: &UserData) {}



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


fn main() {}